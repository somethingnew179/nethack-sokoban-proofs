/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons162
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22820 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (5 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22819 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22821 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (5 : Int) + d1294 pattern := by
  omega
theorem c22822 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (5 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22820 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22821 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22823 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (5 : Int) + d117 pattern := by
  omega
theorem c22824 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (5 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13045 pattern childGuard
    simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22823 pattern childGuard
    simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22825 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (5 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22815 pattern childGuard
    simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22824 pattern childGuard
    simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22826 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (5 : Int) + d1280 pattern := by
  omega
theorem c22827 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (5 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22825 pattern childGuard
    simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22826 pattern childGuard
    simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22828 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (5 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22753 pattern childGuard
    simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22827 pattern childGuard
    simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22829 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (5 : Int) + d1296 pattern := by
  omega
theorem c22830 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (5 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22828 pattern childGuard
    simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22829 pattern childGuard
    simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22831 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (5 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22822 pattern childGuard
    simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22830 pattern childGuard
    simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22832 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (5 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22833 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (5 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22757 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22832 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22834 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (5 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22817 pattern childGuard
    simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22833 pattern childGuard
    simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22835 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (5 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22825 pattern childGuard
    simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22834 pattern childGuard
    simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22836 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (5 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22762 pattern childGuard
    simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22835 pattern childGuard
    simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22837 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d817 pattern := by
  omega
theorem c22838 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22743 pattern childGuard
    simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22666 pattern childGuard
    simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22839 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22837 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22838 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22840 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (5 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22839 pattern childGuard
    simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22841 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (5 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22836 pattern childGuard
    simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22840 pattern childGuard
    simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22842 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (5 : Int) + d830 pattern := by
  omega
theorem c22843 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (5 : Int) + d1276 pattern := by
  omega
theorem c22844 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22661 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13006 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22845 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (5 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22843 pattern childGuard
    simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22844 pattern childGuard
    simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22846 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (5 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22833 pattern childGuard
    simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22847 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (5 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22845 pattern childGuard
    simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22846 pattern childGuard
    simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22848 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (5 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22842 pattern childGuard
    simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22847 pattern childGuard
    simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22849 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (5 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22850 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (5 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22849 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13006 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22851 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22774 pattern childGuard
    simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22850 pattern childGuard
    simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22852 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (5 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22851 pattern childGuard
    simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22667 pattern childGuard
    simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22853 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (5 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22852 pattern childGuard
    simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22854 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (5 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22848 pattern childGuard
    simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22853 pattern childGuard
    simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22855 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (5 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22841 pattern childGuard
    simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22854 pattern childGuard
    simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22856 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (5 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22830 pattern childGuard
    simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22857 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (5 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22855 pattern childGuard
    simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22856 pattern childGuard
    simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22858 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (5 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22831 pattern childGuard
    simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22857 pattern childGuard
    simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22859 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (5 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22860 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (5 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22676 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22859 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22861 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (5 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22859 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22862 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (5 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22860 pattern childGuard
    simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22861 pattern childGuard
    simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22863 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (5 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22862 pattern childGuard
    simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22861 pattern childGuard
    simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22864 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (5 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22677 pattern childGuard
    simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22863 pattern childGuard
    simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22865 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (5 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22683 pattern childGuard
    simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22866 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (5 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22865 pattern childGuard
    simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22867 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (5 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22864 pattern childGuard
    simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22866 pattern childGuard
    simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22868 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (5 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22677 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22869 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (5 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22868 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22870 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (5 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22682 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22832 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22871 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (5 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22860 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22870 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22872 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (5 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22861 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22873 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (5 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22871 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22872 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22874 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (5 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22869 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22873 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22875 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (5 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22696 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22876 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (5 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22875 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22877 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (5 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22874 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22876 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22878 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (5 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22867 pattern childGuard
    simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22877 pattern childGuard
    simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22879 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (5 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22832 pattern childGuard
    simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22880 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (5 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22861 pattern childGuard
    simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22879 pattern childGuard
    simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22881 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (5 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22871 pattern childGuard
    simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22880 pattern childGuard
    simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22882 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (5 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22881 pattern childGuard
    simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22883 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (5 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22726 pattern childGuard
    simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22884 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (5 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22883 pattern childGuard
    simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22885 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (5 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22882 pattern childGuard
    simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22884 pattern childGuard
    simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22886 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (5 : Int) + d49 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22726 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22696 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22887 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (5 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22870 pattern childGuard
    simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22844 pattern childGuard
    simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22888 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (5 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22879 pattern childGuard
    simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22889 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (5 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22887 pattern childGuard
    simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22888 pattern childGuard
    simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22890 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (5 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22886 pattern childGuard
    simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22889 pattern childGuard
    simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22891 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (5 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13226 pattern childGuard
    simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22727 pattern childGuard
    simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22892 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (5 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22891 pattern childGuard
    simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22893 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (5 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22890 pattern childGuard
    simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22892 pattern childGuard
    simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22894 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (5 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22885 pattern childGuard
    simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22893 pattern childGuard
    simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22895 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (5 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22877 pattern childGuard
    simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22896 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (5 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22894 pattern childGuard
    simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22895 pattern childGuard
    simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22897 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (5 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22878 pattern childGuard
    simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22896 pattern childGuard
    simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22898 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (5 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22858 pattern childGuard
    simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22897 pattern childGuard
    simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22899 (pattern : Twelve) (guard : d0 pattern = 1) : d1635 pattern ≤ (5 : Int) + d1635 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c22900 (pattern : Twelve) (guard : d1878 pattern = 1) : d1636 pattern ≤ (5 : Int) + d1635 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22898 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22899 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22901 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (5 : Int) + d1324 pattern := by
  omega
theorem c22902 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (5 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12986 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13056 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22903 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (5 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22901 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22902 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22904 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (5 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22743 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22903 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22905 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (5 : Int) + d1650 pattern := by
  omega
theorem c22906 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (5 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22904 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22905 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22907 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (5 : Int) + d1657 pattern := by
  omega
theorem c22908 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (5 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22906 pattern childGuard
    simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22907 pattern childGuard
    simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22909 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (5 : Int) + d1644 pattern := by
  omega
theorem c22910 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (5 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22901 pattern childGuard
    simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22688 pattern childGuard
    simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22911 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (5 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22909 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22910 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22912 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (5 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22837 pattern childGuard
    simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22911 pattern childGuard
    simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22913 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d821 pattern := by
  omega
theorem c22914 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22913 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22775 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22915 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (5 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22914 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1653, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22916 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (5 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22912 pattern childGuard
    simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22915 pattern childGuard
    simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22917 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (5 : Int) + d1289 pattern := by
  omega
theorem c22918 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (5 : Int) + d20 pattern := by
  omega
theorem c22919 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (5 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22918 pattern childGuard
    simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22920 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (5 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22688 pattern childGuard
    simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d128, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22921 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (5 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22919 pattern childGuard
    simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22920 pattern childGuard
    simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22922 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (5 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22917 pattern childGuard
    simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22921 pattern childGuard
    simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22923 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (5 : Int) + d822 pattern := by
  omega
theorem c22924 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (5 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22923 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13159 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22925 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (5 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22924 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22926 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (5 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22922 pattern childGuard
    simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22925 pattern childGuard
    simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22927 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (5 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22916 pattern childGuard
    simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22926 pattern childGuard
    simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22928 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (5 : Int) + d1662 pattern := by
  omega
theorem c22929 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (5 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22927 pattern childGuard
    simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22928 pattern childGuard
    simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22930 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (5 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22908 pattern childGuard
    simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22929 pattern childGuard
    simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22931 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (5 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22902 pattern childGuard
    simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22932 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (5 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13058 pattern childGuard
    simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1650, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22933 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (5 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22931 pattern childGuard
    simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22932 pattern childGuard
    simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22934 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (5 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22902 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22688 pattern childGuard
    simpa only [d1644, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22935 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (5 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22902 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1645, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22936 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (5 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22934 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22935 pattern childGuard
    simpa only [d1647, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22937 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (5 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13210 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22936 pattern childGuard
    simpa only [d1651, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22938 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (5 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22937 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13228 pattern childGuard
    simpa only [d1657, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22939 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (5 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22933 pattern childGuard
    simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22938 pattern childGuard
    simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22940 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (5 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22934 pattern childGuard
    simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22941 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (5 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13226 pattern childGuard
    simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22942 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (5 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22940 pattern childGuard
    simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22941 pattern childGuard
    simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22943 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (5 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22688 pattern childGuard
    simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22944 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (5 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22943 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22920 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22945 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (5 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13227 pattern childGuard
    simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22944 pattern childGuard
    simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22946 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (5 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22945 pattern childGuard
    simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13273 pattern childGuard
    simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22947 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (5 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22942 pattern childGuard
    simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22946 pattern childGuard
    simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22948 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (5 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22938 pattern childGuard
    simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1662, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22949 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (5 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22947 pattern childGuard
    simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22948 pattern childGuard
    simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22950 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (5 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22939 pattern childGuard
    simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22949 pattern childGuard
    simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22951 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (5 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22930 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22950 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22952 (pattern : Twelve) (guard : d0 pattern = 1) : d1826 pattern ≤ (5 : Int) + d1826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c22953 (pattern : Twelve) (guard : d1878 pattern = 1) : d1827 pattern ≤ (5 : Int) + d1826 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22951 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22952 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22954 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (6 : Int) + d806 pattern := by
  omega
theorem c22955 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (6 : Int) + d1267 pattern := by
  omega
theorem c22956 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (6 : Int) + d1636 pattern := by
  omega
theorem c22957 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (6 : Int) + d1827 pattern := by
  omega
theorem c22958 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d0 pattern := by
  omega
theorem c22959 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d1 pattern := by
  change (0 : Int) ≤ (20 : Int) + 1
  decide
end NetHack.Sokoban21.Diagram
