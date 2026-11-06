/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons013
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1960 (pattern : Twelve) (guard : d1849 pattern = 1) : d1380 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1959 pattern childGuard
    simpa only [d1849, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1849, d1380, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1961 (pattern : Twelve) (guard : d1849 pattern = 1) : d1385 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1671 pattern childGuard
    simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1960 pattern childGuard
    simpa only [d1385, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1962 (pattern : Twelve) (guard : d1849 pattern = 1) : d1386 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1742 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1963 (pattern : Twelve) (guard : d1849 pattern = 1) : d1393 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1961 pattern childGuard
    simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1962 pattern childGuard
    simpa only [d1393, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1964 (pattern : Twelve) (guard : d0 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1965 (pattern : Twelve) (guard : d1857 pattern = 1) : d1398 pattern ≤ (0 : Int) + d1435 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1398, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1963 pattern childGuard
    simpa only [d1857, d1398, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1398, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1964 pattern childGuard
    simpa only [d1857, d1398, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1966 (pattern : Twelve) (guard : d1849 pattern = 1) : d1389 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1684 pattern childGuard
    simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1960 pattern childGuard
    simpa only [d1389, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1967 (pattern : Twelve) (guard : d1849 pattern = 1) : d1395 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1966 pattern childGuard
    simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1962 pattern childGuard
    simpa only [d1395, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1968 (pattern : Twelve) (guard : d0 pattern = 1) : d1394 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1969 (pattern : Twelve) (guard : d1857 pattern = 1) : d1399 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1399, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1967 pattern childGuard
    simpa only [d1857, d1399, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1399, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1968 pattern childGuard
    simpa only [d1857, d1399, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1970 (pattern : Twelve) (guard : d1857 pattern = 1) : d1403 pattern ≤ (0 : Int) + d1438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1403, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d1403, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1403, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1969 pattern childGuard
    simpa only [d1403, d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1971 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1972 (pattern : Twelve) (guard : d1848 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d1848, d1279, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1973 (pattern : Twelve) (guard : d1849 pattern = 1) : d1382 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1382, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1972 pattern childGuard
    simpa only [d1849, d1382, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1382, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1849, d1382, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1974 (pattern : Twelve) (guard : d1849 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1387, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1923 pattern childGuard
    simpa only [d1387, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1387, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1973 pattern childGuard
    simpa only [d1387, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1975 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1976 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1975 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1977 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1978 (pattern : Twelve) (guard : d1849 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1977 pattern childGuard
    simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1979 (pattern : Twelve) (guard : d1849 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1974 pattern childGuard
    simpa only [d1394, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1978 pattern childGuard
    simpa only [d1394, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1980 (pattern : Twelve) (guard : d0 pattern = 1) : d1396 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1981 (pattern : Twelve) (guard : d1857 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1400, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1979 pattern childGuard
    simpa only [d1857, d1400, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1400, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1980 pattern childGuard
    simpa only [d1857, d1400, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1982 (pattern : Twelve) (guard : d1857 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1401, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1979 pattern childGuard
    simpa only [d1857, d1401, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1401, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1401, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1983 (pattern : Twelve) (guard : d1857 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1981 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1982 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1984 (pattern : Twelve) (guard : d1857 pattern = 1) : d1405 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1405, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1970 pattern childGuard
    simpa only [d1405, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1405, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1983 pattern childGuard
    simpa only [d1405, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1985 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1283 pattern := by
  omega
theorem c1986 (pattern : Twelve) (guard : d1849 pattern = 1) : d1384 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1985 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1078 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1987 (pattern : Twelve) (guard : d1849 pattern = 1) : d1392 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1986 pattern childGuard
    simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1392, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1988 (pattern : Twelve) (guard : d1849 pattern = 1) : d1397 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1966 pattern childGuard
    simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1987 pattern childGuard
    simpa only [d1397, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1989 (pattern : Twelve) (guard : d1857 pattern = 1) : d1402 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1402, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1988 pattern childGuard
    simpa only [d1857, d1402, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1402, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1968 pattern childGuard
    simpa only [d1857, d1402, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1990 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1991 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1990 pattern childGuard
    simpa only [d1848, d817, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1992 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1991 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1078 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1993 (pattern : Twelve) (guard : d1849 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1992 pattern childGuard
    simpa only [d1388, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1388, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1994 (pattern : Twelve) (guard : d1849 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1974 pattern childGuard
    simpa only [d1394, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1993 pattern childGuard
    simpa only [d1394, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1995 (pattern : Twelve) (guard : d1857 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1400, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1994 pattern childGuard
    simpa only [d1857, d1400, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1400, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1980 pattern childGuard
    simpa only [d1857, d1400, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1996 (pattern : Twelve) (guard : d1857 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1401, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1994 pattern childGuard
    simpa only [d1857, d1401, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1401, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1401, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1997 (pattern : Twelve) (guard : d1857 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1995 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1996 pattern childGuard
    simpa only [d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1998 (pattern : Twelve) (guard : d1857 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1989 pattern childGuard
    simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1997 pattern childGuard
    simpa only [d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1999 (pattern : Twelve) (guard : d1857 pattern = 1) : d1408 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1408, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1984 pattern childGuard
    simpa only [d1408, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1408, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1998 pattern childGuard
    simpa only [d1408, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2000 (pattern : Twelve) (guard : d1857 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1969 pattern childGuard
    simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1983 pattern childGuard
    simpa only [d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2001 (pattern : Twelve) (guard : d1857 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1409, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2000 pattern childGuard
    simpa only [d1409, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1409, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1998 pattern childGuard
    simpa only [d1409, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2002 (pattern : Twelve) (guard : d1857 pattern = 1) : d1410 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1410, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1999 pattern childGuard
    simpa only [d1410, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1410, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2001 pattern childGuard
    simpa only [d1410, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2003 (pattern : Twelve) (guard : d1857 pattern = 1) : d1411 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1411, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2002 pattern childGuard
    simpa only [d1411, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1411, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2001 pattern childGuard
    simpa only [d1411, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2004 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1324 pattern := by
  omega
theorem c2005 (pattern : Twelve) (guard : d1849 pattern = 1) : d1689 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2006 (pattern : Twelve) (guard : d1849 pattern = 1) : d1693 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1742 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2005 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2007 (pattern : Twelve) (guard : d1849 pattern = 1) : d1694 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1800 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2008 (pattern : Twelve) (guard : d1849 pattern = 1) : d1697 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2006 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2007 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2009 (pattern : Twelve) (guard : d0 pattern = 1) : d1698 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2010 (pattern : Twelve) (guard : d1857 pattern = 1) : d1700 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1700, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2008 pattern childGuard
    simpa only [d1857, d1700, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1700, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2009 pattern childGuard
    simpa only [d1857, d1700, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2011 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2012 (pattern : Twelve) (guard : d1848 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2011 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2013 (pattern : Twelve) (guard : d1849 pattern = 1) : d1691 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2014 (pattern : Twelve) (guard : d1849 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1977 pattern childGuard
    simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2013 pattern childGuard
    simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2015 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2016 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2015 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2017 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2016 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2018 (pattern : Twelve) (guard : d1849 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2017 pattern childGuard
    simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2019 (pattern : Twelve) (guard : d1849 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2014 pattern childGuard
    simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2018 pattern childGuard
    simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2020 (pattern : Twelve) (guard : d0 pattern = 1) : d1699 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2021 (pattern : Twelve) (guard : d1857 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1701, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2019 pattern childGuard
    simpa only [d1857, d1701, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1701, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2020 pattern childGuard
    simpa only [d1857, d1701, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2022 (pattern : Twelve) (guard : d1857 pattern = 1) : d1702 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2019 pattern childGuard
    simpa only [d1857, d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2023 (pattern : Twelve) (guard : d1857 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2021 pattern childGuard
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2022 pattern childGuard
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2024 (pattern : Twelve) (guard : d1857 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2010 pattern childGuard
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2023 pattern childGuard
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2025 (pattern : Twelve) (guard : d0 pattern = 1) : d198 pattern ≤ (0 : Int) + d73 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2026 (pattern : Twelve) (guard : d1839 pattern = 1) : d304 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d304, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d304, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d304, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2025 pattern childGuard
    simpa only [d1839, d304, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2027 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d75 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2028 (pattern : Twelve) (guard : d1839 pattern = 1) : d305 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d305, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d1839, d305, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d305, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2027 pattern childGuard
    simpa only [d1839, d305, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2029 (pattern : Twelve) (guard : d1839 pattern = 1) : d320 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d320, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2026 pattern childGuard
    simpa only [d320, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d320, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2028 pattern childGuard
    simpa only [d320, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2030 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d76 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2031 (pattern : Twelve) (guard : d1839 pattern = 1) : d306 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d306, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d306, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d306, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2030 pattern childGuard
    simpa only [d1839, d306, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2032 (pattern : Twelve) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d78 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2033 (pattern : Twelve) (guard : d1839 pattern = 1) : d307 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d307, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d307, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d307, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2032 pattern childGuard
    simpa only [d1839, d307, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2034 (pattern : Twelve) (guard : d1839 pattern = 1) : d321 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d321, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2031 pattern childGuard
    simpa only [d321, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d321, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2033 pattern childGuard
    simpa only [d321, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2035 (pattern : Twelve) (guard : d1839 pattern = 1) : d332 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d332, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2029 pattern childGuard
    simpa only [d332, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d332, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2034 pattern childGuard
    simpa only [d332, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2036 (pattern : Twelve) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d80 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2037 (pattern : Twelve) (guard : d1839 pattern = 1) : d308 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d308, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c436 pattern childGuard
    simpa only [d1839, d308, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d308, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2036 pattern childGuard
    simpa only [d1839, d308, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2038 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d82 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2039 (pattern : Twelve) (guard : d1839 pattern = 1) : d309 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d309, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c439 pattern childGuard
    simpa only [d1839, d309, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d309, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2038 pattern childGuard
    simpa only [d1839, d309, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2040 (pattern : Twelve) (guard : d1839 pattern = 1) : d322 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d322, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2037 pattern childGuard
    simpa only [d322, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d322, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2039 pattern childGuard
    simpa only [d322, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2041 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d78 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2042 (pattern : Twelve) (guard : d1839 pattern = 1) : d310 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d310, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d310, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d310, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2041 pattern childGuard
    simpa only [d1839, d310, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2043 (pattern : Twelve) (guard : d1839 pattern = 1) : d323 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d323, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2042 pattern childGuard
    simpa only [d323, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d323, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d323, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2044 (pattern : Twelve) (guard : d1839 pattern = 1) : d333 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d333, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2040 pattern childGuard
    simpa only [d333, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d333, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2043 pattern childGuard
    simpa only [d333, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2045 (pattern : Twelve) (guard : d1839 pattern = 1) : d338 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d338, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2035 pattern childGuard
    simpa only [d338, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d338, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d338, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2046 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d80 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2047 (pattern : Twelve) (guard : d1839 pattern = 1) : d311 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d311, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d311, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d311, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2046 pattern childGuard
    simpa only [d1839, d311, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2048 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d84 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2049 (pattern : Twelve) (guard : d1839 pattern = 1) : d312 pattern ≤ (0 : Int) + d98 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d312, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c451 pattern childGuard
    simpa only [d1839, d312, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d312, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2048 pattern childGuard
    simpa only [d1839, d312, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2050 (pattern : Twelve) (guard : d1839 pattern = 1) : d324 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d324, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2047 pattern childGuard
    simpa only [d324, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d324, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2049 pattern childGuard
    simpa only [d324, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2051 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d86 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2052 (pattern : Twelve) (guard : d1839 pattern = 1) : d313 pattern ≤ (0 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d313, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c455 pattern childGuard
    simpa only [d1839, d313, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d313, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2051 pattern childGuard
    simpa only [d1839, d313, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2053 (pattern : Twelve) (guard : d1839 pattern = 1) : d325 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d325, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2047 pattern childGuard
    simpa only [d325, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d325, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2052 pattern childGuard
    simpa only [d325, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2054 (pattern : Twelve) (guard : d1839 pattern = 1) : d334 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d334, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2050 pattern childGuard
    simpa only [d334, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d334, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2053 pattern childGuard
    simpa only [d334, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2055 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d88 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2056 (pattern : Twelve) (guard : d1839 pattern = 1) : d314 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d314, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c460 pattern childGuard
    simpa only [d1839, d314, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d314, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2055 pattern childGuard
    simpa only [d1839, d314, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2057 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d90 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2058 (pattern : Twelve) (guard : d1839 pattern = 1) : d315 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d315, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c463 pattern childGuard
    simpa only [d1839, d315, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d315, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2057 pattern childGuard
    simpa only [d1839, d315, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2059 (pattern : Twelve) (guard : d1839 pattern = 1) : d326 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d326, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d326, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d326, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2058 pattern childGuard
    simpa only [d326, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2060 (pattern : Twelve) (guard : d1839 pattern = 1) : d327 pattern ≤ (0 : Int) + d109 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d327, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2052 pattern childGuard
    simpa only [d327, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d327, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d327, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2061 (pattern : Twelve) (guard : d1839 pattern = 1) : d335 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d335, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2059 pattern childGuard
    simpa only [d335, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d335, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2060 pattern childGuard
    simpa only [d335, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2062 (pattern : Twelve) (guard : d1839 pattern = 1) : d339 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d339, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2054 pattern childGuard
    simpa only [d339, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d339, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2061 pattern childGuard
    simpa only [d339, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2063 (pattern : Twelve) (guard : d1839 pattern = 1) : d341 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d341, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2045 pattern childGuard
    simpa only [d341, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d341, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2062 pattern childGuard
    simpa only [d341, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2064 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d73 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2065 (pattern : Twelve) (guard : d1839 pattern = 1) : d311 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d311, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d311, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d311, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2064 pattern childGuard
    simpa only [d1839, d311, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2066 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d75 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2067 (pattern : Twelve) (guard : d1839 pattern = 1) : d316 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d316, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d1839, d316, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d316, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2066 pattern childGuard
    simpa only [d1839, d316, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2068 (pattern : Twelve) (guard : d1839 pattern = 1) : d328 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d328, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2065 pattern childGuard
    simpa only [d328, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d328, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2067 pattern childGuard
    simpa only [d328, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2069 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d76 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2070 (pattern : Twelve) (guard : d1839 pattern = 1) : d311 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d311, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d311, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d311, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2069 pattern childGuard
    simpa only [d1839, d311, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2071 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d78 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2072 (pattern : Twelve) (guard : d1839 pattern = 1) : d317 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d317, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d317, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d317, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2071 pattern childGuard
    simpa only [d1839, d317, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2073 (pattern : Twelve) (guard : d1839 pattern = 1) : d329 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d329, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2070 pattern childGuard
    simpa only [d329, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d329, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2072 pattern childGuard
    simpa only [d329, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2074 (pattern : Twelve) (guard : d1839 pattern = 1) : d336 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d336, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2068 pattern childGuard
    simpa only [d336, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d336, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2073 pattern childGuard
    simpa only [d336, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2075 (pattern : Twelve) (guard : d1839 pattern = 1) : d318 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d318, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c436 pattern childGuard
    simpa only [d1839, d318, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d318, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2046 pattern childGuard
    simpa only [d1839, d318, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2076 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d82 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2077 (pattern : Twelve) (guard : d1839 pattern = 1) : d319 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d319, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c439 pattern childGuard
    simpa only [d1839, d319, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d319, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2076 pattern childGuard
    simpa only [d1839, d319, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2078 (pattern : Twelve) (guard : d1839 pattern = 1) : d330 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d330, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2075 pattern childGuard
    simpa only [d330, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d330, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2077 pattern childGuard
    simpa only [d330, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2079 (pattern : Twelve) (guard : d1839 pattern = 1) : d331 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d331, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2072 pattern childGuard
    simpa only [d331, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d331, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d331, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2080 (pattern : Twelve) (guard : d1839 pattern = 1) : d337 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d337, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2078 pattern childGuard
    simpa only [d337, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d337, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2079 pattern childGuard
    simpa only [d337, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2081 (pattern : Twelve) (guard : d1839 pattern = 1) : d340 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d340, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2074 pattern childGuard
    simpa only [d340, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d340, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2080 pattern childGuard
    simpa only [d340, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2082 (pattern : Twelve) (guard : d1839 pattern = 1) : d342 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d342, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2081 pattern childGuard
    simpa only [d342, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d342, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2062 pattern childGuard
    simpa only [d342, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2083 (pattern : Twelve) (guard : d1839 pattern = 1) : d343 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2063 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2082 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2084 (pattern : Twelve) (guard : d1839 pattern = 1) : d344 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2083 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2082 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2085 (pattern : Twelve) (guard : d0 pattern = 1) : d909 pattern ≤ (0 : Int) + d839 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2086 (pattern : Twelve) (guard : d1839 pattern = 1) : d980 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d980, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d980, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d980, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2085 pattern childGuard
    simpa only [d1839, d980, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2087 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d841 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2088 (pattern : Twelve) (guard : d1839 pattern = 1) : d981 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d981, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d1839, d981, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d981, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2087 pattern childGuard
    simpa only [d1839, d981, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2089 (pattern : Twelve) (guard : d1839 pattern = 1) : d991 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d991, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2086 pattern childGuard
    simpa only [d991, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d991, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2088 pattern childGuard
    simpa only [d991, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2090 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d839 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2091 (pattern : Twelve) (guard : d1839 pattern = 1) : d982 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d982, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d982, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d982, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2090 pattern childGuard
    simpa only [d1839, d982, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2092 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d841 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2093 (pattern : Twelve) (guard : d1839 pattern = 1) : d983 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d983, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d1839, d983, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d983, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2092 pattern childGuard
    simpa only [d1839, d983, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2094 (pattern : Twelve) (guard : d1839 pattern = 1) : d992 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d992, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2091 pattern childGuard
    simpa only [d992, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d992, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2093 pattern childGuard
    simpa only [d992, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2095 (pattern : Twelve) (guard : d1839 pattern = 1) : d1000 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2089 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2094 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2096 (pattern : Twelve) (guard : d0 pattern = 1) : d911 pattern ≤ (0 : Int) + d843 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2097 (pattern : Twelve) (guard : d1839 pattern = 1) : d984 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d984, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d1839, d984, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d984, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2096 pattern childGuard
    simpa only [d1839, d984, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2098 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d845 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2099 (pattern : Twelve) (guard : d1839 pattern = 1) : d985 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d985, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c508 pattern childGuard
    simpa only [d1839, d985, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d985, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2098 pattern childGuard
    simpa only [d1839, d985, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
