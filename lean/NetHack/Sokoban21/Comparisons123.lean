/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons122
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17220 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17133 pattern childGuard
    simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17219 pattern childGuard
    simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17221 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16987 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17222 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17221 pattern childGuard
    simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17223 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17220 pattern childGuard
    simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17222 pattern childGuard
    simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17224 (pattern : Twelve) (guard : d1848 pattern = 1) : d1459 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17216 pattern childGuard
    simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17223 pattern childGuard
    simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17225 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17124 pattern childGuard
    simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17212 pattern childGuard
    simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17226 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17225 pattern childGuard
    simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17215 pattern childGuard
    simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17227 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17226 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17223 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17228 (pattern : Twelve) (guard : d1848 pattern = 1) : d1463 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17224 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17227 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17229 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17210 pattern childGuard
    simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17190 pattern childGuard
    simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17230 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17217 pattern childGuard
    simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17229 pattern childGuard
    simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17231 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17230 pattern childGuard
    simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17232 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17233 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17231 pattern childGuard
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17232 pattern childGuard
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17234 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (1 : Int) + d1276 pattern := by
  omega
theorem c17235 (pattern : Twelve) (guard : d1848 pattern = 1) : d1330 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17234 pattern childGuard
    simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11270 pattern childGuard
    simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17236 (pattern : Twelve) (guard : d1848 pattern = 1) : d1446 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17235 pattern childGuard
    simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17103 pattern childGuard
    simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17237 (pattern : Twelve) (guard : d1848 pattern = 1) : d1451 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17153 pattern childGuard
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17236 pattern childGuard
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17238 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11145 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17041 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17239 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17238 pattern childGuard
    simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17240 (pattern : Twelve) (guard : d1848 pattern = 1) : d1457 pattern ≤ (1 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17237 pattern childGuard
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17239 pattern childGuard
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17241 (pattern : Twelve) (guard : d1848 pattern = 1) : d1460 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17233 pattern childGuard
    simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17240 pattern childGuard
    simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17242 (pattern : Twelve) (guard : d1848 pattern = 1) : d1461 pattern ≤ (1 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17223 pattern childGuard
    simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17243 (pattern : Twelve) (guard : d1848 pattern = 1) : d1464 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17241 pattern childGuard
    simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17242 pattern childGuard
    simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17244 (pattern : Twelve) (guard : d1848 pattern = 1) : d1466 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17228 pattern childGuard
    simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17243 pattern childGuard
    simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17245 (pattern : Twelve) (guard : d1848 pattern = 1) : d1467 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17227 pattern childGuard
    simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17243 pattern childGuard
    simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17246 (pattern : Twelve) (guard : d1848 pattern = 1) : d1469 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17244 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17245 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17247 (pattern : Twelve) (guard : d1848 pattern = 1) : d1470 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17246 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17245 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17248 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17208 pattern childGuard
    simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17249 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17210 pattern childGuard
    simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17250 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17248 pattern childGuard
    simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17249 pattern childGuard
    simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17251 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17124 pattern childGuard
    simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17250 pattern childGuard
    simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17252 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17251 pattern childGuard
    simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17215 pattern childGuard
    simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17253 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17208 pattern childGuard
    simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17190 pattern childGuard
    simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17254 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17253 pattern childGuard
    simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17218 pattern childGuard
    simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17255 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17133 pattern childGuard
    simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17254 pattern childGuard
    simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17256 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17255 pattern childGuard
    simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17222 pattern childGuard
    simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17257 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17252 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17256 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17258 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17210 pattern childGuard
    simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11270 pattern childGuard
    simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17259 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17253 pattern childGuard
    simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17258 pattern childGuard
    simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17260 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17259 pattern childGuard
    simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17261 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11348 pattern childGuard
    simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17262 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17261 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17263 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17262 pattern childGuard
    simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17264 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17260 pattern childGuard
    simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17263 pattern childGuard
    simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17265 (pattern : Twelve) (guard : d1848 pattern = 1) : d1337 pattern ≤ (1 : Int) + d1337 pattern := by
  omega
theorem c17266 (pattern : Twelve) (guard : d1848 pattern = 1) : d1453 pattern ≤ (1 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17153 pattern childGuard
    simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17265 pattern childGuard
    simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17267 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11143 pattern childGuard
    simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17268 (pattern : Twelve) (guard : d1848 pattern = 1) : d1447 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17267 pattern childGuard
    simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17110 pattern childGuard
    simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17269 (pattern : Twelve) (guard : d1848 pattern = 1) : d1454 pattern ≤ (1 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17268 pattern childGuard
    simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17270 (pattern : Twelve) (guard : d1848 pattern = 1) : d1458 pattern ≤ (1 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17266 pattern childGuard
    simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17269 pattern childGuard
    simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17271 (pattern : Twelve) (guard : d1848 pattern = 1) : d1462 pattern ≤ (1 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17264 pattern childGuard
    simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17270 pattern childGuard
    simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17272 (pattern : Twelve) (guard : d1848 pattern = 1) : d1461 pattern ≤ (1 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17256 pattern childGuard
    simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17273 (pattern : Twelve) (guard : d1848 pattern = 1) : d1465 pattern ≤ (1 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17271 pattern childGuard
    simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17272 pattern childGuard
    simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17274 (pattern : Twelve) (guard : d1848 pattern = 1) : d1468 pattern ≤ (1 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17257 pattern childGuard
    simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17273 pattern childGuard
    simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17275 (pattern : Twelve) (guard : d1848 pattern = 1) : d1471 pattern ≤ (1 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17247 pattern childGuard
    simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17274 pattern childGuard
    simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17276 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (1 : Int) + d1324 pattern := by
  omega
theorem c17277 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17276 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17278 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17214 pattern childGuard
    simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17277 pattern childGuard
    simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17279 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11143 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17280 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (1 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17279 pattern childGuard
    simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17281 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17278 pattern childGuard
    simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17280 pattern childGuard
    simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17282 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17276 pattern childGuard
    simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11348 pattern childGuard
    simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17283 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1645 pattern := by
  omega
theorem c17284 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17282 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17283 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17285 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17221 pattern childGuard
    simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17284 pattern childGuard
    simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17286 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17285 pattern childGuard
    simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17239 pattern childGuard
    simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17287 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17281 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17286 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17288 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17282 pattern childGuard
    simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17289 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11145 pattern childGuard
    simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17290 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17288 pattern childGuard
    simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17289 pattern childGuard
    simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17291 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (1 : Int) + d20 pattern := by
  omega
theorem c17292 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17291 pattern childGuard
    simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17293 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17292 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17110 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17294 (pattern : Twelve) (guard : d1848 pattern = 1) : d1717 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17238 pattern childGuard
    simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17293 pattern childGuard
    simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17295 (pattern : Twelve) (guard : d1848 pattern = 1) : d1655 pattern ≤ (1 : Int) + d1655 pattern := by
  omega
theorem c17296 (pattern : Twelve) (guard : d1848 pattern = 1) : d1720 pattern ≤ (1 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17294 pattern childGuard
    simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17295 pattern childGuard
    simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17297 (pattern : Twelve) (guard : d1848 pattern = 1) : d1722 pattern ≤ (1 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17290 pattern childGuard
    simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17296 pattern childGuard
    simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17298 (pattern : Twelve) (guard : d1848 pattern = 1) : d1723 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17286 pattern childGuard
    simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17299 (pattern : Twelve) (guard : d1848 pattern = 1) : d1725 pattern ≤ (1 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17297 pattern childGuard
    simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17298 pattern childGuard
    simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17300 (pattern : Twelve) (guard : d1848 pattern = 1) : d1727 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17287 pattern childGuard
    simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17299 pattern childGuard
    simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17301 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (1 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17214 pattern childGuard
    simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17282 pattern childGuard
    simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17302 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17301 pattern childGuard
    simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17280 pattern childGuard
    simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17303 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17302 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17286 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17304 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17276 pattern childGuard
    simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17305 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17282 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17304 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17306 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (1 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11069 pattern childGuard
    simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17305 pattern childGuard
    simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17307 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (1 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17306 pattern childGuard
    simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17239 pattern childGuard
    simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17308 (pattern : Twelve) (guard : d1848 pattern = 1) : d1667 pattern ≤ (1 : Int) + d1667 pattern := by
  omega
theorem c17309 (pattern : Twelve) (guard : d1848 pattern = 1) : d1718 pattern ≤ (1 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17238 pattern childGuard
    simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17308 pattern childGuard
    simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17310 (pattern : Twelve) (guard : d1848 pattern = 1) : d1626 pattern ≤ (1 : Int) + d1626 pattern := by
  omega
theorem c17311 (pattern : Twelve) (guard : d1848 pattern = 1) : d1721 pattern ≤ (1 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17309 pattern childGuard
    simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17310 pattern childGuard
    simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17312 (pattern : Twelve) (guard : d1848 pattern = 1) : d1724 pattern ≤ (1 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17307 pattern childGuard
    simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17311 pattern childGuard
    simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17313 (pattern : Twelve) (guard : d1848 pattern = 1) : d1726 pattern ≤ (1 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17312 pattern childGuard
    simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17298 pattern childGuard
    simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17314 (pattern : Twelve) (guard : d1848 pattern = 1) : d1728 pattern ≤ (1 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17303 pattern childGuard
    simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17313 pattern childGuard
    simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17315 (pattern : Twelve) (guard : d1848 pattern = 1) : d1729 pattern ≤ (1 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17300 pattern childGuard
    simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17314 pattern childGuard
    simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17316 (pattern : Twelve) (guard : d0 pattern = 1) : d50 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17317 (pattern : Twelve) (guard : d1852 pattern = 1) : d72 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11974 pattern childGuard
    simpa only [d1852, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17316 pattern childGuard
    simpa only [d1852, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17318 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17319 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) ≤ (1 : Int) + 3
  decide
theorem c17320 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17319 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17321 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17318 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17320 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17322 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17321 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17323 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17319 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17324 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11222 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17323 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17325 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17324 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11403 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17326 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17322 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17325 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17327 (pattern : Twelve) (guard : d0 pattern = 1) : d51 pattern ≤ (1 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17328 (pattern : Twelve) (guard : d1852 pattern = 1) : d73 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17326 pattern childGuard
    simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17327 pattern childGuard
    simpa only [d1852, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17329 (pattern : Twelve) (guard : d1852 pattern = 1) : d91 pattern ≤ (1 : Int) + d3161 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17317 pattern childGuard
    simpa only [d91, d3161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17328 pattern childGuard
    simpa only [d91, d3161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17330 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (1 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d31, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11394 pattern childGuard
    simpa only [d31, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17331 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17330 pattern childGuard
    simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17332 (pattern : Twelve) (guard : d0 pattern = 1) : d53 pattern ≤ (1 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17333 (pattern : Twelve) (guard : d1852 pattern = 1) : d74 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17331 pattern childGuard
    simpa only [d1852, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17332 pattern childGuard
    simpa only [d1852, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17334 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11139 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17335 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17324 pattern childGuard
    simpa only [d33, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d33, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17336 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17335 pattern childGuard
    simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17337 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (1 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17338 (pattern : Twelve) (guard : d1852 pattern = 1) : d75 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17336 pattern childGuard
    simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17337 pattern childGuard
    simpa only [d1852, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17339 (pattern : Twelve) (guard : d1852 pattern = 1) : d92 pattern ≤ (1 : Int) + d3162 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17333 pattern childGuard
    simpa only [d92, d3162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17338 pattern childGuard
    simpa only [d92, d3162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17340 (pattern : Twelve) (guard : d1852 pattern = 1) : d102 pattern ≤ (1 : Int) + d3163 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17329 pattern childGuard
    simpa only [d102, d3163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17339 pattern childGuard
    simpa only [d102, d3163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17341 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17320 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17342 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17341 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17343 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17342 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17325 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17344 (pattern : Twelve) (guard : d1852 pattern = 1) : d76 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17343 pattern childGuard
    simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17337 pattern childGuard
    simpa only [d1852, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17345 (pattern : Twelve) (guard : d1852 pattern = 1) : d93 pattern ≤ (1 : Int) + d3164 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17317 pattern childGuard
    simpa only [d93, d3164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17344 pattern childGuard
    simpa only [d93, d3164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17346 (pattern : Twelve) (guard : d0 pattern = 1) : d57 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17347 (pattern : Twelve) (guard : d1852 pattern = 1) : d77 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11990 pattern childGuard
    simpa only [d1852, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17346 pattern childGuard
    simpa only [d1852, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17348 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17324 pattern childGuard
    simpa only [d35, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d35, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17349 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d56, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17348 pattern childGuard
    simpa only [d56, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17350 (pattern : Twelve) (guard : d1852 pattern = 1) : d78 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17349 pattern childGuard
    simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17337 pattern childGuard
    simpa only [d1852, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17351 (pattern : Twelve) (guard : d1852 pattern = 1) : d94 pattern ≤ (1 : Int) + d3165 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17347 pattern childGuard
    simpa only [d94, d3165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17350 pattern childGuard
    simpa only [d94, d3165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17352 (pattern : Twelve) (guard : d1852 pattern = 1) : d103 pattern ≤ (1 : Int) + d3166 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17345 pattern childGuard
    simpa only [d103, d3166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17351 pattern childGuard
    simpa only [d103, d3166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17353 (pattern : Twelve) (guard : d1852 pattern = 1) : d110 pattern ≤ (1 : Int) + d3167 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17340 pattern childGuard
    simpa only [d110, d3167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17352 pattern childGuard
    simpa only [d110, d3167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17354 (pattern : Twelve) (guard : d0 pattern = 1) : d58 pattern ≤ (1 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17355 (pattern : Twelve) (guard : d1852 pattern = 1) : d79 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11998 pattern childGuard
    simpa only [d1852, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17354 pattern childGuard
    simpa only [d1852, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17356 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17324 pattern childGuard
    simpa only [d30, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d30, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17357 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17356 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17358 (pattern : Twelve) (guard : d1852 pattern = 1) : d80 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17357 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17337 pattern childGuard
    simpa only [d1852, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17359 (pattern : Twelve) (guard : d1852 pattern = 1) : d95 pattern ≤ (1 : Int) + d3168 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17355 pattern childGuard
    simpa only [d95, d3168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17358 pattern childGuard
    simpa only [d95, d3168, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
