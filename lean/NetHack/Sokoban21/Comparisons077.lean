/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons076
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10780 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (3 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10763 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10779 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10781 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (3 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10702 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10780 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10782 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (3 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10696 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10783 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (3 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10685 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10782 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10784 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (3 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10783 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10757 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10785 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (3 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10781 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10784 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10786 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (3 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10778 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10785 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10787 (pattern : Twelve) (guard : d1836 pattern = 1) : d864 pattern ≤ (3 : Int) + d1316 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10775 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10786 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10788 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d1317 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10789 (pattern : Twelve) (guard : d1890 pattern = 1) : d1012 pattern ≤ (3 : Int) + d1895 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1012, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10787 pattern childGuard
    simpa only [d1890, d1012, d1895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1012, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10788 pattern childGuard
    simpa only [d1890, d1012, d1895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10790 (pattern : Twelve) (guard : d1890 pattern = 1) : d1014 pattern ≤ (3 : Int) + d1896 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1014, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10774 pattern childGuard
    simpa only [d1014, d1896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1014, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10789 pattern childGuard
    simpa only [d1014, d1896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10791 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d1314 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10792 (pattern : Twelve) (guard : d1890 pattern = 1) : d1013 pattern ≤ (3 : Int) + d1894 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1013, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10772 pattern childGuard
    simpa only [d1890, d1013, d1894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1013, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10791 pattern childGuard
    simpa only [d1890, d1013, d1894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10793 (pattern : Twelve) (guard : d1890 pattern = 1) : d1015 pattern ≤ (3 : Int) + d1896 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1015, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10792 pattern childGuard
    simpa only [d1015, d1896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1015, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10789 pattern childGuard
    simpa only [d1015, d1896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10794 (pattern : Twelve) (guard : d1890 pattern = 1) : d1016 pattern ≤ (3 : Int) + d1896 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10790 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10793 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10795 (pattern : Twelve) (guard : d1890 pattern = 1) : d1017 pattern ≤ (3 : Int) + d1896 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10794 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10793 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10796 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (3 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10797 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (3 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10733 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10679 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10798 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (3 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10676 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10797 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10799 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (3 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10666 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10675 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10800 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (3 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10799 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10797 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10801 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (3 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10798 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10800 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10802 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (3 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10801 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10800 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10803 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (3 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10677 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10802 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10804 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (3 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10688 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10805 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (3 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10803 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10804 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10806 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (3 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10760 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10750 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10807 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (3 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10683 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10806 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10808 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (3 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10798 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10807 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10809 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (3 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10800 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10810 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (3 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10808 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10809 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10811 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (3 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10768 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10810 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10812 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (3 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10679 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10750 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10813 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (3 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10682 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10752 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10814 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (3 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10812 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10813 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10815 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (3 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10688 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10814 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10816 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (3 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10815 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10690 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10817 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (3 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10816 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10818 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (3 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10811 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10817 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10819 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (3 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10805 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10818 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10820 (pattern : Twelve) (guard : d1836 pattern = 1) : d1313 pattern ≤ (3 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10796 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10819 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10821 (pattern : Twelve) (guard : d0 pattern = 1) : d1363 pattern ≤ (3 : Int) + d1661 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10822 (pattern : Twelve) (guard : d1890 pattern = 1) : d1428 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1428, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10820 pattern childGuard
    simpa only [d1890, d1428, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1428, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10821 pattern childGuard
    simpa only [d1890, d1428, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10823 (pattern : Twelve) (guard : d0 pattern = 1) : d1316 pattern ≤ (3 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10824 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (3 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10688 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10684 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10825 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (3 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10824 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10826 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (3 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10803 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10825 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10827 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (3 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10815 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10718 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10828 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (3 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10827 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10829 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (3 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10811 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10828 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10830 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (3 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10826 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10829 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10831 (pattern : Twelve) (guard : d1836 pattern = 1) : d1316 pattern ≤ (3 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10823 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10830 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10832 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d1661 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10833 (pattern : Twelve) (guard : d1890 pattern = 1) : d1429 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1429, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10831 pattern childGuard
    simpa only [d1890, d1429, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1429, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10832 pattern childGuard
    simpa only [d1890, d1429, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10834 (pattern : Twelve) (guard : d1890 pattern = 1) : d1431 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10822 pattern childGuard
    simpa only [d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10833 pattern childGuard
    simpa only [d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10835 (pattern : Twelve) (guard : d1890 pattern = 1) : d1430 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1430, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10820 pattern childGuard
    simpa only [d1890, d1430, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1430, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10832 pattern childGuard
    simpa only [d1890, d1430, d1897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10836 (pattern : Twelve) (guard : d1890 pattern = 1) : d1432 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10835 pattern childGuard
    simpa only [d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10833 pattern childGuard
    simpa only [d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10837 (pattern : Twelve) (guard : d1890 pattern = 1) : d1433 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10834 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10836 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10838 (pattern : Twelve) (guard : d1890 pattern = 1) : d1434 pattern ≤ (3 : Int) + d1897 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10837 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1890 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10836 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10839 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (3 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10840 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10748 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10751 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10841 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10749 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10840 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10842 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10754 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10843 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10841 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10842 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10844 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10749 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10845 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10755 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10844 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10846 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10750 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10847 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10753 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10846 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10848 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10840 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10847 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10849 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10840 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10850 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10848 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10849 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10851 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10845 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10850 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10852 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10752 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10853 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10846 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10852 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10854 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10754 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10853 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10855 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10854 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10756 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10856 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10855 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10689 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10857 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10851 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10856 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10858 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10843 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10857 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10859 (pattern : Twelve) (guard : d1836 pattern = 1) : d1660 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10839 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10858 pattern childGuard
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10860 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (3 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10861 (pattern : Twelve) (guard : d1890 pattern = 1) : d1714 pattern ≤ (3 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10859 pattern childGuard
    simpa only [d1890, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10860 pattern childGuard
    simpa only [d1890, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10862 (pattern : Twelve) (guard : d0 pattern = 1) : d102 pattern ≤ (0 : Int) + d104 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10863 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem c10864 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10865 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d2 pattern := by
  change (1 : Int) ≤ (0 : Int) + 2
  decide
theorem c10866 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10867 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d3 pattern := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem c10868 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d27, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10869 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10866 pattern childGuard
    simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10868 pattern childGuard
    simpa only [d50, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10870 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10864 pattern childGuard
    simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10869 pattern childGuard
    simpa only [d72, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10871 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (0 : Int) + d55 pattern := by
  omega
theorem c10872 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10864 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10871 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10873 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10870 pattern childGuard
    simpa only [d93, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10872 pattern childGuard
    simpa only [d93, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10874 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem c10875 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10876 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c10877 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10878 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10875 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10877 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10879 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10880 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10879 pattern childGuard
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10881 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10880 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10882 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10875 pattern childGuard
    simpa only [d57, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10881 pattern childGuard
    simpa only [d57, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10883 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10878 pattern childGuard
    simpa only [d77, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10882 pattern childGuard
    simpa only [d77, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10884 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d5 pattern := by
  change (3 : Int) ≤ (0 : Int) + 5
  decide
theorem c10885 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10886 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10885 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10887 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10880 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10886 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10888 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10889 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10890 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10888 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10889 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10891 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10890 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10892 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10887 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10891 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10893 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10878 pattern childGuard
    simpa only [d78, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10892 pattern childGuard
    simpa only [d78, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10894 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10883 pattern childGuard
    simpa only [d94, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10893 pattern childGuard
    simpa only [d94, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10895 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10873 pattern childGuard
    simpa only [d103, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10894 pattern childGuard
    simpa only [d103, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10896 (pattern : Twelve) (guard : d1836 pattern = 1) : d110 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10862 pattern childGuard
    simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10895 pattern childGuard
    simpa only [d1836, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10897 (pattern : Twelve) (guard : d0 pattern = 1) : d111 pattern ≤ (0 : Int) + d104 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10898 (pattern : Twelve) (guard : d1890 pattern = 1) : d114 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1836 pattern = 1 := by simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10896 pattern childGuard
    simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10897 pattern childGuard
    simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10899 (pattern : Twelve) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d108 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10900 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem c10901 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10902 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10903 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (0 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10902 pattern childGuard
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10904 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (0 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10866 pattern childGuard
    simpa only [d50, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10903 pattern childGuard
    simpa only [d50, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10905 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10864 pattern childGuard
    simpa only [d72, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10904 pattern childGuard
    simpa only [d72, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10906 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10875 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10907 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10908 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10909 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10907 pattern childGuard
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10908 pattern childGuard
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10910 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10909 pattern childGuard
    simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10911 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10910 pattern childGuard
    simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10912 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (0 : Int) + d88 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10906 pattern childGuard
    simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10911 pattern childGuard
    simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10913 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10905 pattern childGuard
    simpa only [d97, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10912 pattern childGuard
    simpa only [d97, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10914 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (0 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10915 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10875 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10914 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10916 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10878 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10915 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10917 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10918 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10875 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10917 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10919 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (0 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10886 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
