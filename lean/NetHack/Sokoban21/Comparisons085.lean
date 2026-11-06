/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons084
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11900 (pattern : Twelve) (guard : d0 pattern = 1) : d1072 pattern ≤ (1 : Int) + d1651 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11901 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1286 pattern := by
  omega
theorem c11902 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1647 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11903 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11901 pattern childGuard
    simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11902 pattern childGuard
    simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11904 (pattern : Twelve) (guard : d1999 pattern = 1) : d1473 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11900 pattern childGuard
    simpa only [d1999, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11903 pattern childGuard
    simpa only [d1999, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11905 (pattern : Twelve) (guard : d1999 pattern = 1) : d1479 pattern ≤ (1 : Int) + d2016 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1479, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11899 pattern childGuard
    simpa only [d1479, d2016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1479, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11904 pattern childGuard
    simpa only [d1479, d2016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11906 (pattern : Twelve) (guard : d0 pattern = 1) : d1073 pattern ≤ (1 : Int) + d1649 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11907 (pattern : Twelve) (guard : d1999 pattern = 1) : d1474 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11906 pattern childGuard
    simpa only [d1999, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11898 pattern childGuard
    simpa only [d1999, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11908 (pattern : Twelve) (guard : d1999 pattern = 1) : d1480 pattern ≤ (1 : Int) + d2016 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1480, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11907 pattern childGuard
    simpa only [d1480, d2016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1480, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11904 pattern childGuard
    simpa only [d1480, d2016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11909 (pattern : Twelve) (guard : d1999 pattern = 1) : d1484 pattern ≤ (1 : Int) + d2016 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11905 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11908 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11910 (pattern : Twelve) (guard : d0 pattern = 1) : d1074 pattern ≤ (1 : Int) + d1652 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11911 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d817 pattern := by
  omega
theorem c11912 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11913 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11911 pattern childGuard
    simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11912 pattern childGuard
    simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11914 (pattern : Twelve) (guard : d1999 pattern = 1) : d1475 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11910 pattern childGuard
    simpa only [d1999, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11913 pattern childGuard
    simpa only [d1999, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11915 (pattern : Twelve) (guard : d0 pattern = 1) : d1075 pattern ≤ (1 : Int) + d1654 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11916 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1289 pattern := by
  omega
theorem c11917 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1648 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11918 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11916 pattern childGuard
    simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11917 pattern childGuard
    simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11919 (pattern : Twelve) (guard : d1999 pattern = 1) : d1476 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11915 pattern childGuard
    simpa only [d1999, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11918 pattern childGuard
    simpa only [d1999, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11920 (pattern : Twelve) (guard : d1999 pattern = 1) : d1481 pattern ≤ (1 : Int) + d2017 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1481, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11914 pattern childGuard
    simpa only [d1481, d2017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1481, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11919 pattern childGuard
    simpa only [d1481, d2017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11921 (pattern : Twelve) (guard : d1999 pattern = 1) : d1482 pattern ≤ (1 : Int) + d2018 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1482, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11904 pattern childGuard
    simpa only [d1482, d2018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1482, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1482, d2018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11922 (pattern : Twelve) (guard : d1999 pattern = 1) : d1485 pattern ≤ (1 : Int) + d2019 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1485, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11920 pattern childGuard
    simpa only [d1485, d2019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1485, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11921 pattern childGuard
    simpa only [d1485, d2019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11923 (pattern : Twelve) (guard : d1999 pattern = 1) : d1487 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1487, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11909 pattern childGuard
    simpa only [d1487, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1487, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11922 pattern childGuard
    simpa only [d1487, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11924 (pattern : Twelve) (guard : d1999 pattern = 1) : d1488 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1488, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11908 pattern childGuard
    simpa only [d1488, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1488, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11922 pattern childGuard
    simpa only [d1488, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11925 (pattern : Twelve) (guard : d1999 pattern = 1) : d1490 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11923 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11924 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11926 (pattern : Twelve) (guard : d1999 pattern = 1) : d1491 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11925 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11924 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11927 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11928 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11911 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11927 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11929 (pattern : Twelve) (guard : d1852 pattern = 1) : d1342 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1342, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11928 pattern childGuard
    simpa only [d1852, d1342, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1342, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11912 pattern childGuard
    simpa only [d1852, d1342, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11930 (pattern : Twelve) (guard : d1999 pattern = 1) : d1477 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11910 pattern childGuard
    simpa only [d1999, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11929 pattern childGuard
    simpa only [d1999, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11931 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11932 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11387 pattern childGuard
    simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11931 pattern childGuard
    simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11933 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11143 pattern childGuard
    simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11932 pattern childGuard
    simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11934 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d128, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11935 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11933 pattern childGuard
    simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11934 pattern childGuard
    simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11936 (pattern : Twelve) (guard : d1852 pattern = 1) : d1344 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1344, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11935 pattern childGuard
    simpa only [d1852, d1344, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1344, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11917 pattern childGuard
    simpa only [d1852, d1344, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11937 (pattern : Twelve) (guard : d1999 pattern = 1) : d1478 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11915 pattern childGuard
    simpa only [d1999, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11936 pattern childGuard
    simpa only [d1999, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11938 (pattern : Twelve) (guard : d1999 pattern = 1) : d1483 pattern ≤ (1 : Int) + d2017 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1483, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11930 pattern childGuard
    simpa only [d1483, d2017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1483, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11937 pattern childGuard
    simpa only [d1483, d2017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11939 (pattern : Twelve) (guard : d1999 pattern = 1) : d1486 pattern ≤ (1 : Int) + d2019 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1486, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11938 pattern childGuard
    simpa only [d1486, d2019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1486, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11921 pattern childGuard
    simpa only [d1486, d2019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11940 (pattern : Twelve) (guard : d1999 pattern = 1) : d1489 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1489, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11908 pattern childGuard
    simpa only [d1489, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1489, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11939 pattern childGuard
    simpa only [d1489, d2020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11941 (pattern : Twelve) (guard : d1999 pattern = 1) : d1492 pattern ≤ (1 : Int) + d2020 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11926 pattern childGuard
    simpa only [d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11940 pattern childGuard
    simpa only [d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11942 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11943 (pattern : Twelve) (guard : d1852 pattern = 1) : d1650 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11944 (pattern : Twelve) (guard : d1999 pattern = 1) : d1730 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11942 pattern childGuard
    simpa only [d1999, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11943 pattern childGuard
    simpa only [d1999, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11945 (pattern : Twelve) (guard : d0 pattern = 1) : d1296 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11946 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11947 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11948 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11946 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11947 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11949 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11948 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11950 (pattern : Twelve) (guard : d1999 pattern = 1) : d1731 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11945 pattern childGuard
    simpa only [d1999, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11949 pattern childGuard
    simpa only [d1999, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11951 (pattern : Twelve) (guard : d1999 pattern = 1) : d1736 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11944 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11950 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11952 (pattern : Twelve) (guard : d0 pattern = 1) : d1298 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11953 (pattern : Twelve) (guard : d1852 pattern = 1) : d1653 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11946 pattern childGuard
    simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11954 (pattern : Twelve) (guard : d1999 pattern = 1) : d1732 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11952 pattern childGuard
    simpa only [d1999, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11953 pattern childGuard
    simpa only [d1999, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11955 (pattern : Twelve) (guard : d0 pattern = 1) : d1300 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11956 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11957 (pattern : Twelve) (guard : d1852 pattern = 1) : d1655 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11956 pattern childGuard
    simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11958 (pattern : Twelve) (guard : d1999 pattern = 1) : d1733 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11955 pattern childGuard
    simpa only [d1999, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11957 pattern childGuard
    simpa only [d1999, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11959 (pattern : Twelve) (guard : d1999 pattern = 1) : d1737 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11954 pattern childGuard
    simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11958 pattern childGuard
    simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11960 (pattern : Twelve) (guard : d1999 pattern = 1) : d1738 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11950 pattern childGuard
    simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11961 (pattern : Twelve) (guard : d1999 pattern = 1) : d1740 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11959 pattern childGuard
    simpa only [d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11960 pattern childGuard
    simpa only [d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11962 (pattern : Twelve) (guard : d1999 pattern = 1) : d1742 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11951 pattern childGuard
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11961 pattern childGuard
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11963 (pattern : Twelve) (guard : d1999 pattern = 1) : d1734 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11952 pattern childGuard
    simpa only [d1999, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11949 pattern childGuard
    simpa only [d1999, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11964 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11956 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11965 (pattern : Twelve) (guard : d1852 pattern = 1) : d1626 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11964 pattern childGuard
    simpa only [d1852, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1852, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11966 (pattern : Twelve) (guard : d1999 pattern = 1) : d1735 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11955 pattern childGuard
    simpa only [d1999, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11965 pattern childGuard
    simpa only [d1999, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11967 (pattern : Twelve) (guard : d1999 pattern = 1) : d1739 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11963 pattern childGuard
    simpa only [d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11966 pattern childGuard
    simpa only [d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11968 (pattern : Twelve) (guard : d1999 pattern = 1) : d1741 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11967 pattern childGuard
    simpa only [d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11960 pattern childGuard
    simpa only [d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11969 (pattern : Twelve) (guard : d1999 pattern = 1) : d1743 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11951 pattern childGuard
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11968 pattern childGuard
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11970 (pattern : Twelve) (guard : d1999 pattern = 1) : d1744 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11962 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11969 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11971 (pattern : Twelve) (guard : d0 pattern = 1) : d72 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11972 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11973 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11974 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11972 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11973 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11975 (pattern : Twelve) (guard : d0 pattern = 1) : d51 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11976 (pattern : Twelve) (guard : d1852 pattern = 1) : d73 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11974 pattern childGuard
    simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11975 pattern childGuard
    simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11977 (pattern : Twelve) (guard : d1999 pattern = 1) : d91 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11971 pattern childGuard
    simpa only [d1999, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11976 pattern childGuard
    simpa only [d1999, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11978 (pattern : Twelve) (guard : d0 pattern = 1) : d74 pattern ≤ (1 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11979 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (1 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d33, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11932 pattern childGuard
    simpa only [d33, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11980 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d54, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11979 pattern childGuard
    simpa only [d54, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11981 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (1 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11982 (pattern : Twelve) (guard : d1852 pattern = 1) : d75 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11980 pattern childGuard
    simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11981 pattern childGuard
    simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11983 (pattern : Twelve) (guard : d1999 pattern = 1) : d92 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11978 pattern childGuard
    simpa only [d1999, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11982 pattern childGuard
    simpa only [d1999, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11984 (pattern : Twelve) (guard : d1999 pattern = 1) : d102 pattern ≤ (1 : Int) + d2021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d102, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11977 pattern childGuard
    simpa only [d102, d2021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d102, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11983 pattern childGuard
    simpa only [d102, d2021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11985 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11986 (pattern : Twelve) (guard : d1852 pattern = 1) : d76 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11974 pattern childGuard
    simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11985 pattern childGuard
    simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11987 (pattern : Twelve) (guard : d1999 pattern = 1) : d93 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11971 pattern childGuard
    simpa only [d1999, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11986 pattern childGuard
    simpa only [d1999, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11988 (pattern : Twelve) (guard : d0 pattern = 1) : d77 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11989 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11990 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11989 pattern childGuard
    simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11991 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11992 (pattern : Twelve) (guard : d1852 pattern = 1) : d78 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11990 pattern childGuard
    simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11991 pattern childGuard
    simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11993 (pattern : Twelve) (guard : d1999 pattern = 1) : d94 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11988 pattern childGuard
    simpa only [d1999, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11992 pattern childGuard
    simpa only [d1999, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11994 (pattern : Twelve) (guard : d1999 pattern = 1) : d103 pattern ≤ (1 : Int) + d2022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d103, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11987 pattern childGuard
    simpa only [d103, d2022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d103, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11993 pattern childGuard
    simpa only [d103, d2022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11995 (pattern : Twelve) (guard : d1999 pattern = 1) : d110 pattern ≤ (1 : Int) + d2023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d110, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11984 pattern childGuard
    simpa only [d110, d2023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d110, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11994 pattern childGuard
    simpa only [d110, d2023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11996 (pattern : Twelve) (guard : d0 pattern = 1) : d79 pattern ≤ (1 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11997 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d30, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11998 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11997 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11999 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (1 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12000 (pattern : Twelve) (guard : d1852 pattern = 1) : d80 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11998 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11999 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12001 (pattern : Twelve) (guard : d1999 pattern = 1) : d95 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11996 pattern childGuard
    simpa only [d1999, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12000 pattern childGuard
    simpa only [d1999, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12002 (pattern : Twelve) (guard : d0 pattern = 1) : d81 pattern ≤ (1 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12003 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (1 : Int) + d38 pattern := by
  omega
theorem c12004 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12005 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12003 pattern childGuard
    simpa only [d59, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12004 pattern childGuard
    simpa only [d59, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12006 (pattern : Twelve) (guard : d0 pattern = 1) : d61 pattern ≤ (1 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12007 (pattern : Twelve) (guard : d1852 pattern = 1) : d82 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12005 pattern childGuard
    simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12006 pattern childGuard
    simpa only [d1852, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12008 (pattern : Twelve) (guard : d1999 pattern = 1) : d96 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12002 pattern childGuard
    simpa only [d1999, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12007 pattern childGuard
    simpa only [d1999, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12009 (pattern : Twelve) (guard : d1999 pattern = 1) : d104 pattern ≤ (1 : Int) + d2024 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d104, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12001 pattern childGuard
    simpa only [d104, d2024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d104, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12008 pattern childGuard
    simpa only [d104, d2024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12010 (pattern : Twelve) (guard : d1999 pattern = 1) : d105 pattern ≤ (1 : Int) + d2025 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d105, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11993 pattern childGuard
    simpa only [d105, d2025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d105, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d105, d2025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12011 (pattern : Twelve) (guard : d1999 pattern = 1) : d111 pattern ≤ (1 : Int) + d2026 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d111, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12009 pattern childGuard
    simpa only [d111, d2026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d111, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12010 pattern childGuard
    simpa only [d111, d2026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12012 (pattern : Twelve) (guard : d1999 pattern = 1) : d114 pattern ≤ (1 : Int) + d2027 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d114, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11995 pattern childGuard
    simpa only [d114, d2027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d114, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12011 pattern childGuard
    simpa only [d114, d2027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12013 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d1 pattern := by
  change (2 : Int) ≤ (1 : Int) + 1
  decide
theorem c12014 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12015 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d30, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12016 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12014 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12015 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12017 (pattern : Twelve) (guard : d1852 pattern = 1) : d80 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12016 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11985 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12018 (pattern : Twelve) (guard : d1999 pattern = 1) : d97 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11971 pattern childGuard
    simpa only [d1999, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12017 pattern childGuard
    simpa only [d1999, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12019 (pattern : Twelve) (guard : d0 pattern = 1) : d83 pattern ≤ (1 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12020 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (1 : Int) + d43 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d44, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11932 pattern childGuard
    simpa only [d44, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12021 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (1 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d63, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12020 pattern childGuard
    simpa only [d63, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12022 (pattern : Twelve) (guard : d0 pattern = 1) : d64 pattern ≤ (1 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12023 (pattern : Twelve) (guard : d1852 pattern = 1) : d84 pattern ≤ (1 : Int) + d62 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12021 pattern childGuard
    simpa only [d1852, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12022 pattern childGuard
    simpa only [d1852, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12024 (pattern : Twelve) (guard : d1999 pattern = 1) : d98 pattern ≤ (1 : Int) + d62 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12019 pattern childGuard
    simpa only [d1999, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12023 pattern childGuard
    simpa only [d1999, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12025 (pattern : Twelve) (guard : d1999 pattern = 1) : d106 pattern ≤ (1 : Int) + d2028 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d106, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12018 pattern childGuard
    simpa only [d106, d2028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d106, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12024 pattern childGuard
    simpa only [d106, d2028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12026 (pattern : Twelve) (guard : d0 pattern = 1) : d85 pattern ≤ (1 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12027 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d39, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d39, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12028 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d66, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12027 pattern childGuard
    simpa only [d66, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12029 (pattern : Twelve) (guard : d0 pattern = 1) : d64 pattern ≤ (1 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12030 (pattern : Twelve) (guard : d1852 pattern = 1) : d86 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12028 pattern childGuard
    simpa only [d1852, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12029 pattern childGuard
    simpa only [d1852, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12031 (pattern : Twelve) (guard : d1999 pattern = 1) : d99 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12026 pattern childGuard
    simpa only [d1999, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12030 pattern childGuard
    simpa only [d1999, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12032 (pattern : Twelve) (guard : d1999 pattern = 1) : d107 pattern ≤ (1 : Int) + d2029 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d107, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12018 pattern childGuard
    simpa only [d107, d2029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d107, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12031 pattern childGuard
    simpa only [d107, d2029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12033 (pattern : Twelve) (guard : d1999 pattern = 1) : d112 pattern ≤ (1 : Int) + d2030 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d112, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12025 pattern childGuard
    simpa only [d112, d2030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d112, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12032 pattern childGuard
    simpa only [d112, d2030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12034 (pattern : Twelve) (guard : d0 pattern = 1) : d87 pattern ≤ (1 : Int) + d67 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12035 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d38, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d38, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12036 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d68, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12035 pattern childGuard
    simpa only [d68, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12037 (pattern : Twelve) (guard : d0 pattern = 1) : d64 pattern ≤ (1 : Int) + d67 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12038 (pattern : Twelve) (guard : d1852 pattern = 1) : d88 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12036 pattern childGuard
    simpa only [d1852, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12037 pattern childGuard
    simpa only [d1852, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12039 (pattern : Twelve) (guard : d1999 pattern = 1) : d100 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12034 pattern childGuard
    simpa only [d1999, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12038 pattern childGuard
    simpa only [d1999, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
