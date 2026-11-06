/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38780 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38779 p hg
    simpa only [d8091, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38781 (p : Pattern) (guard : d8092 p = 1) : d1851 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38777 p hg
    simpa only [d8092, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38780 p hg
    simpa only [d8092, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38782 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d8091, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38783 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d8085, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38784 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38783 p hg
    simpa only [d8090, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38785 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38784 p hg
    simpa only [d8095, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38786 (p : Pattern) (guard : d8096 p = 1) : d1692 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38782 p hg
    simpa only [d8096, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38785 p hg
    simpa only [d8096, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38787 (p : Pattern) (guard : d8097 p = 1) : d1852 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38781 p hg
    simpa only [d8097, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38786 p hg
    simpa only [d8097, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38788 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34756 p hg
    simpa only [d8095, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38789 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38788 p hg
    simpa only [d8101, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38790 (p : Pattern) (guard : d8102 p = 1) : d1699 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38666 p hg
    simpa only [d8102, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38789 p hg
    simpa only [d8102, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38791 (p : Pattern) (guard : d8103 p = 1) : d1853 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38787 p hg
    simpa only [d8103, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38790 p hg
    simpa only [d8103, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38792 (p : Pattern) (guard : d8102 p = 1) : d1699 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38635 p hg
    simpa only [d8102, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38675 p hg
    simpa only [d8102, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38793 (p : Pattern) (guard : d8095 p = 1) : d25 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34765 p hg
    simpa only [d8095, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38794 (p : Pattern) (guard : d8101 p = 1) : d1706 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38793 p hg
    simpa only [d8101, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38795 (p : Pattern) (guard : d8107 p = 1) : d1707 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38794 p hg
    simpa only [d8107, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38796 (p : Pattern) (guard : d8108 p = 1) : d1708 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38792 p hg
    simpa only [d8108, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38795 p hg
    simpa only [d8108, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38797 (p : Pattern) (guard : d8109 p = 1) : d1854 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38791 p hg
    simpa only [d8109, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38796 p hg
    simpa only [d8109, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38798 (p : Pattern) (guard : d8096 p = 1) : d1719 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d8096, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38799 (p : Pattern) (guard : d8101 p = 1) : d1726 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8101, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38800 (p : Pattern) (guard : d8102 p = 1) : d1727 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38798 p hg
    simpa only [d8102, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38799 p hg
    simpa only [d8102, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38801 (p : Pattern) (guard : d8101 p = 1) : d1731 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8101, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38802 (p : Pattern) (guard : d8107 p = 1) : d1733 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38801 p hg
    simpa only [d8107, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8107, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38803 (p : Pattern) (guard : d8108 p = 1) : d1734 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38800 p hg
    simpa only [d8108, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38802 p hg
    simpa only [d8108, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38804 (p : Pattern) (guard : d8114 p = 1) : d1738 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38803 p hg
    simpa only [d8114, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38662 p hg
    simpa only [d8114, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38805 (p : Pattern) (guard : d8115 p = 1) : d1855 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38797 p hg
    simpa only [d8115, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38804 p hg
    simpa only [d8115, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38806 (p : Pattern) (guard : d8090 p = 1) : d333 p ≤ (0 : Int) + d333 p := by
  omega
theorem compare38807 (p : Pattern) (guard : d8091 p = 1) : d1689 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34779 p hg
    simpa only [d8091, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38806 p hg
    simpa only [d8091, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38808 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d8085, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38809 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38808 p hg
    simpa only [d8090, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38810 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38809 p hg
    simpa only [d8095, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38811 (p : Pattern) (guard : d8096 p = 1) : d1690 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38807 p hg
    simpa only [d8096, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38810 p hg
    simpa only [d8096, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38812 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34786 p hg
    simpa only [d8095, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38813 (p : Pattern) (guard : d8101 p = 1) : d1747 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38812 p hg
    simpa only [d8101, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38814 (p : Pattern) (guard : d8102 p = 1) : d1856 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38811 p hg
    simpa only [d8102, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38813 p hg
    simpa only [d8102, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38815 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34791 p hg
    simpa only [d8095, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38816 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38815 p hg
    simpa only [d8101, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38817 (p : Pattern) (guard : d8100 p = 1) : d25 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34796 p hg
    simpa only [d8100, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38818 (p : Pattern) (guard : d8106 p = 1) : d1706 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38817 p hg
    simpa only [d8106, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38819 (p : Pattern) (guard : d8107 p = 1) : d1749 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38816 p hg
    simpa only [d8107, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38818 p hg
    simpa only [d8107, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38820 (p : Pattern) (guard : d8108 p = 1) : d1857 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38814 p hg
    simpa only [d8108, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38819 p hg
    simpa only [d8108, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38821 (p : Pattern) (guard : d8100 p = 1) : d59 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34804 p hg
    simpa only [d8100, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38822 (p : Pattern) (guard : d8106 p = 1) : d1754 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38821 p hg
    simpa only [d8106, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38823 (p : Pattern) (guard : d8107 p = 1) : d1755 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38789 p hg
    simpa only [d8107, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38822 p hg
    simpa only [d8107, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38824 (p : Pattern) (guard : d8113 p = 1) : d1758 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38823 p hg
    simpa only [d8113, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38825 (p : Pattern) (guard : d8114 p = 1) : d1858 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38820 p hg
    simpa only [d8114, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38824 p hg
    simpa only [d8114, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38826 (p : Pattern) (guard : d8101 p = 1) : d1726 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38827 (p : Pattern) (guard : d8107 p = 1) : d1761 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38826 p hg
    simpa only [d8107, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38686 p hg
    simpa only [d8107, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38828 (p : Pattern) (guard : d8113 p = 1) : d1763 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38827 p hg
    simpa only [d8113, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38689 p hg
    simpa only [d8113, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38829 (p : Pattern) (guard : d8119 p = 1) : d1766 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38828 p hg
    simpa only [d8119, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38695 p hg
    simpa only [d8119, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38830 (p : Pattern) (guard : d8120 p = 1) : d1859 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38825 p hg
    simpa only [d8120, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38829 p hg
    simpa only [d8120, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38831 (p : Pattern) (guard : d8121 p = 1) : d1860 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38805 p hg
    simpa only [d8121, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38830 p hg
    simpa only [d8121, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38832 (p : Pattern) (guard : d8096 p = 1) : d1774 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38596 p hg
    simpa only [d8096, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38833 (p : Pattern) (guard : d8102 p = 1) : d1784 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38832 p hg
    simpa only [d8102, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38767 p hg
    simpa only [d8102, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38834 (p : Pattern) (guard : d8101 p = 1) : d1790 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8101, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38835 (p : Pattern) (guard : d8107 p = 1) : d1800 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38834 p hg
    simpa only [d8107, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8107, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38836 (p : Pattern) (guard : d8108 p = 1) : d1801 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38833 p hg
    simpa only [d8108, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38835 p hg
    simpa only [d8108, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38837 (p : Pattern) (guard : d8113 p = 1) : d1807 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38763 p hg
    simpa only [d8113, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38725 p hg
    simpa only [d8113, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38838 (p : Pattern) (guard : d8114 p = 1) : d1808 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38836 p hg
    simpa only [d8114, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38837 p hg
    simpa only [d8114, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38839 (p : Pattern) (guard : d8120 p = 1) : d1814 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38838 p hg
    simpa only [d8120, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38736 p hg
    simpa only [d8120, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38840 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8101, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38841 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34833 p hg
    simpa only [d8100, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38842 (p : Pattern) (guard : d8106 p = 1) : d1809 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38841 p hg
    simpa only [d8106, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38843 (p : Pattern) (guard : d8107 p = 1) : d1815 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38840 p hg
    simpa only [d8107, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38842 p hg
    simpa only [d8107, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38844 (p : Pattern) (guard : d8113 p = 1) : d1817 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38843 p hg
    simpa only [d8113, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38746 p hg
    simpa only [d8113, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38845 (p : Pattern) (guard : d8119 p = 1) : d1820 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38844 p hg
    simpa only [d8119, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38752 p hg
    simpa only [d8119, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38846 (p : Pattern) (guard : d8125 p = 1) : d1824 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38845 p hg
    simpa only [d8125, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d8125, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38847 (p : Pattern) (guard : d8126 p = 1) : d1825 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38839 p hg
    simpa only [d8126, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38846 p hg
    simpa only [d8126, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38848 (p : Pattern) (guard : d8127 p = 1) : d1861 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38831 p hg
    simpa only [d8127, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38847 p hg
    simpa only [d8127, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38849 (p : Pattern) (guard : d8096 p = 1) : d1774 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38665 p hg
    simpa only [d8096, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38850 (p : Pattern) (guard : d8102 p = 1) : d1784 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38849 p hg
    simpa only [d8102, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38840 p hg
    simpa only [d8102, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38851 (p : Pattern) (guard : d8101 p = 1) : d1790 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38852 (p : Pattern) (guard : d8107 p = 1) : d1800 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38851 p hg
    simpa only [d8107, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8107, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38853 (p : Pattern) (guard : d8108 p = 1) : d1801 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38850 p hg
    simpa only [d8108, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38852 p hg
    simpa only [d8108, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38854 (p : Pattern) (guard : d8113 p = 1) : d1807 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38835 p hg
    simpa only [d8113, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38725 p hg
    simpa only [d8113, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38855 (p : Pattern) (guard : d8114 p = 1) : d1808 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38853 p hg
    simpa only [d8114, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38854 p hg
    simpa only [d8114, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38856 (p : Pattern) (guard : d8101 p = 1) : d1809 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38463 p hg
    simpa only [d8101, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38857 (p : Pattern) (guard : d8107 p = 1) : d1811 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38856 p hg
    simpa only [d8107, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38733 p hg
    simpa only [d8107, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38858 (p : Pattern) (guard : d8113 p = 1) : d1812 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38857 p hg
    simpa only [d8113, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38859 (p : Pattern) (guard : d8119 p = 1) : d1813 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38858 p hg
    simpa only [d8119, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38860 (p : Pattern) (guard : d8120 p = 1) : d1814 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38855 p hg
    simpa only [d8120, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38859 p hg
    simpa only [d8120, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38861 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d8101, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38862 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35017 p hg
    simpa only [d8100, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38863 (p : Pattern) (guard : d8106 p = 1) : d1809 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38862 p hg
    simpa only [d8106, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38864 (p : Pattern) (guard : d8107 p = 1) : d1815 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38861 p hg
    simpa only [d8107, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38863 p hg
    simpa only [d8107, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38865 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34851 p hg
    simpa only [d8100, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38866 (p : Pattern) (guard : d8106 p = 1) : d1799 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38865 p hg
    simpa only [d8106, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38867 (p : Pattern) (guard : d8112 p = 1) : d1816 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38866 p hg
    simpa only [d8112, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38745 p hg
    simpa only [d8112, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38868 (p : Pattern) (guard : d8113 p = 1) : d1817 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38864 p hg
    simpa only [d8113, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38867 p hg
    simpa only [d8113, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38869 (p : Pattern) (guard : d8119 p = 1) : d1820 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38868 p hg
    simpa only [d8119, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38752 p hg
    simpa only [d8119, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38870 (p : Pattern) (guard : d8125 p = 1) : d1824 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38869 p hg
    simpa only [d8125, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d8125, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38871 (p : Pattern) (guard : d8126 p = 1) : d1825 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38860 p hg
    simpa only [d8126, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38870 p hg
    simpa only [d8126, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38872 (p : Pattern) (guard : d8101 p = 1) : d1805 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38793 p hg
    simpa only [d8101, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38873 (p : Pattern) (guard : d8107 p = 1) : d1827 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38872 p hg
    simpa only [d8107, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38570 p hg
    simpa only [d8107, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38874 (p : Pattern) (guard : d8113 p = 1) : d1828 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38873 p hg
    simpa only [d8113, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38875 (p : Pattern) (guard : d8118 p = 1) : d1829 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8118, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38876 (p : Pattern) (guard : d8119 p = 1) : d1830 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38874 p hg
    simpa only [d8119, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38875 p hg
    simpa only [d8119, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38877 (p : Pattern) (guard : d8124 p = 1) : d1831 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38875 p hg
    simpa only [d8124, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38878 (p : Pattern) (guard : d8125 p = 1) : d1832 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38876 p hg
    simpa only [d8125, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38877 p hg
    simpa only [d8125, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38879 (p : Pattern) (guard : d8130 p = 1) : d1833 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38877 p hg
    simpa only [d8130, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38880 (p : Pattern) (guard : d8131 p = 1) : d1834 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38878 p hg
    simpa only [d8131, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38879 p hg
    simpa only [d8131, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38881 (p : Pattern) (guard : d8132 p = 1) : d1835 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38871 p hg
    simpa only [d8132, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38880 p hg
    simpa only [d8132, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38882 (p : Pattern) (guard : d8133 p = 1) : d1862 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38848 p hg
    simpa only [d8133, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38881 p hg
    simpa only [d8133, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38883 (p : Pattern) (guard : d8089 p = 1) : d1685 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8089, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d8089, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38884 (p : Pattern) (guard : d5854 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38885 (p : Pattern) (guard : d8094 p = 1) : d1686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38883 p hg
    simpa only [d8094, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d8094, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38886 (p : Pattern) (guard : d8100 p = 1) : d1687 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38885 p hg
    simpa only [d8100, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38887 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d8101, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38888 (p : Pattern) (guard : d8102 p = 1) : d1692 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38786 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38887 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38889 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8101, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38890 (p : Pattern) (guard : d5854 p = 1) : d1695 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d5854, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d5854, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38891 (p : Pattern) (guard : d8099 p = 1) : d1696 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38890 p hg
    simpa only [d8099, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d8099, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38892 (p : Pattern) (guard : d8105 p = 1) : d1697 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38891 p hg
    simpa only [d8105, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38893 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38865 p hg
    simpa only [d8106, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38894 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38889 p hg
    simpa only [d8107, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38893 p hg
    simpa only [d8107, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38895 (p : Pattern) (guard : d8108 p = 1) : d1863 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1863, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38888 p hg
    simpa only [d8108, d1863, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1863, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38894 p hg
    simpa only [d8108, d1863, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38896 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1692, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d1692, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38897 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8106, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38898 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38896 p hg
    simpa only [d8107, d1699, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38897 p hg
    simpa only [d8107, d1699, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38899 (p : Pattern) (guard : d8112 p = 1) : d1707 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38679 p hg
    simpa only [d8112, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38900 (p : Pattern) (guard : d8113 p = 1) : d1708 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1708, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38898 p hg
    simpa only [d8113, d1708, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1708, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38899 p hg
    simpa only [d8113, d1708, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38901 (p : Pattern) (guard : d8114 p = 1) : d1864 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1864, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38895 p hg
    simpa only [d8114, d1864, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1864, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38900 p hg
    simpa only [d8114, d1864, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38902 (p : Pattern) (guard : d8101 p = 1) : d1719 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1719, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8101, d1719, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1719, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1719, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38903 (p : Pattern) (guard : d8106 p = 1) : d1726 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8106, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38904 (p : Pattern) (guard : d8107 p = 1) : d1727 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1727, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38902 p hg
    simpa only [d8107, d1727, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1727, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38903 p hg
    simpa only [d8107, d1727, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38905 (p : Pattern) (guard : d8106 p = 1) : d1731 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8106, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38906 (p : Pattern) (guard : d8111 p = 1) : d1732 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8111, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38907 (p : Pattern) (guard : d8112 p = 1) : d1733 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38905 p hg
    simpa only [d8112, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8112, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38908 (p : Pattern) (guard : d8113 p = 1) : d1734 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1734, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38904 p hg
    simpa only [d8113, d1734, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1734, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38907 p hg
    simpa only [d8113, d1734, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38909 (p : Pattern) (guard : d8106 p = 1) : d1735 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8106, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38910 (p : Pattern) (guard : d8112 p = 1) : d1736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38909 p hg
    simpa only [d8112, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8112, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38911 (p : Pattern) (guard : d8117 p = 1) : d528 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38688 p hg
    simpa only [d8117, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38912 (p : Pattern) (guard : d8118 p = 1) : d1737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38910 p hg
    simpa only [d8118, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38911 p hg
    simpa only [d8118, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38913 (p : Pattern) (guard : d8119 p = 1) : d1738 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1738, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38908 p hg
    simpa only [d8119, d1738, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1738, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38912 p hg
    simpa only [d8119, d1738, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38914 (p : Pattern) (guard : d8120 p = 1) : d1865 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1865, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38901 p hg
    simpa only [d8120, d1865, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1865, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38913 p hg
    simpa only [d8120, d1865, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38915 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38916 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38915 p hg
    simpa only [d8101, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38917 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d8100, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38918 (p : Pattern) (guard : d5854 p = 1) : d1744 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d5854, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d5854, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38919 (p : Pattern) (guard : d8099 p = 1) : d1745 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38918 p hg
    simpa only [d8099, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d8099, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
