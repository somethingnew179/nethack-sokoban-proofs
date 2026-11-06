/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons051
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7280 (pattern : Twelve) (guard : d1865 pattern = 1) : d1496 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7281 (pattern : Twelve) (guard : d1865 pattern = 1) : d1506 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7279 pattern childGuard
    simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7280 pattern childGuard
    simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7282 (pattern : Twelve) (guard : d1865 pattern = 1) : d1519 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7194 pattern childGuard
    simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7281 pattern childGuard
    simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7283 (pattern : Twelve) (guard : d1865 pattern = 1) : d1507 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7004 pattern childGuard
    simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7284 (pattern : Twelve) (guard : d1865 pattern = 1) : d1520 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7283 pattern childGuard
    simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7285 (pattern : Twelve) (guard : d1865 pattern = 1) : d1533 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7282 pattern childGuard
    simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7284 pattern childGuard
    simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7286 (pattern : Twelve) (guard : d1865 pattern = 1) : d1541 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7277 pattern childGuard
    simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7285 pattern childGuard
    simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7287 (pattern : Twelve) (guard : d1865 pattern = 1) : d1521 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7274 pattern childGuard
    simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7288 (pattern : Twelve) (guard : d1865 pattern = 1) : d1534 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7287 pattern childGuard
    simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7276 pattern childGuard
    simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7289 (pattern : Twelve) (guard : d1865 pattern = 1) : d1542 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7288 pattern childGuard
    simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7285 pattern childGuard
    simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7290 (pattern : Twelve) (guard : d1865 pattern = 1) : d1548 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7286 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7289 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7291 (pattern : Twelve) (guard : d1865 pattern = 1) : d1497 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7162 pattern childGuard
    simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7292 (pattern : Twelve) (guard : d1865 pattern = 1) : d1508 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7279 pattern childGuard
    simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7291 pattern childGuard
    simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7293 (pattern : Twelve) (guard : d1865 pattern = 1) : d1522 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7292 pattern childGuard
    simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7294 (pattern : Twelve) (guard : d1865 pattern = 1) : d1523 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7295 (pattern : Twelve) (guard : d1865 pattern = 1) : d1535 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7293 pattern childGuard
    simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7294 pattern childGuard
    simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7296 (pattern : Twelve) (guard : d1865 pattern = 1) : d1493 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3159 pattern childGuard
    simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7297 (pattern : Twelve) (guard : d1865 pattern = 1) : d1498 pattern ≤ (0 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7278 pattern childGuard
    simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7296 pattern childGuard
    simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7298 (pattern : Twelve) (guard : d1865 pattern = 1) : d1509 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7297 pattern childGuard
    simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7163 pattern childGuard
    simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7299 (pattern : Twelve) (guard : d1865 pattern = 1) : d1524 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7215 pattern childGuard
    simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7298 pattern childGuard
    simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7300 (pattern : Twelve) (guard : d1865 pattern = 1) : d1510 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7216 pattern childGuard
    simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7091 pattern childGuard
    simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7301 (pattern : Twelve) (guard : d1865 pattern = 1) : d1525 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7300 pattern childGuard
    simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7302 (pattern : Twelve) (guard : d1865 pattern = 1) : d1536 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7299 pattern childGuard
    simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7301 pattern childGuard
    simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7303 (pattern : Twelve) (guard : d1865 pattern = 1) : d1543 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7295 pattern childGuard
    simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7302 pattern childGuard
    simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7304 (pattern : Twelve) (guard : d1865 pattern = 1) : d1544 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7285 pattern childGuard
    simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7305 (pattern : Twelve) (guard : d1865 pattern = 1) : d1549 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7303 pattern childGuard
    simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7304 pattern childGuard
    simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7306 (pattern : Twelve) (guard : d1865 pattern = 1) : d1551 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7290 pattern childGuard
    simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7305 pattern childGuard
    simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7307 (pattern : Twelve) (guard : d1865 pattern = 1) : d1552 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7289 pattern childGuard
    simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7305 pattern childGuard
    simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7308 (pattern : Twelve) (guard : d1865 pattern = 1) : d1554 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7306 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7307 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7309 (pattern : Twelve) (guard : d1865 pattern = 1) : d1555 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7308 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7307 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7310 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d16 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7311 (pattern : Twelve) (guard : d1865 pattern = 1) : d1494 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3174 pattern childGuard
    simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7310 pattern childGuard
    simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7312 (pattern : Twelve) (guard : d1865 pattern = 1) : d1499 pattern ≤ (0 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7272 pattern childGuard
    simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7313 (pattern : Twelve) (guard : d1865 pattern = 1) : d1500 pattern ≤ (0 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7314 (pattern : Twelve) (guard : d1865 pattern = 1) : d1511 pattern ≤ (0 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7312 pattern childGuard
    simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7313 pattern childGuard
    simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7315 (pattern : Twelve) (guard : d1865 pattern = 1) : d1526 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7314 pattern childGuard
    simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7316 (pattern : Twelve) (guard : d1865 pattern = 1) : d1537 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7315 pattern childGuard
    simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7276 pattern childGuard
    simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7317 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (0 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7272 pattern childGuard
    simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7162 pattern childGuard
    simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7318 (pattern : Twelve) (guard : d1865 pattern = 1) : d1512 pattern ≤ (0 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7317 pattern childGuard
    simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7280 pattern childGuard
    simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7319 (pattern : Twelve) (guard : d1865 pattern = 1) : d1527 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7194 pattern childGuard
    simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7318 pattern childGuard
    simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7320 (pattern : Twelve) (guard : d1865 pattern = 1) : d1538 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7319 pattern childGuard
    simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7284 pattern childGuard
    simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7321 (pattern : Twelve) (guard : d1865 pattern = 1) : d1545 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7316 pattern childGuard
    simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7320 pattern childGuard
    simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7322 (pattern : Twelve) (guard : d1865 pattern = 1) : d1501 pattern ≤ (0 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7296 pattern childGuard
    simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7323 (pattern : Twelve) (guard : d1865 pattern = 1) : d1513 pattern ≤ (0 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7317 pattern childGuard
    simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7322 pattern childGuard
    simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7324 (pattern : Twelve) (guard : d1865 pattern = 1) : d1528 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7323 pattern childGuard
    simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7325 (pattern : Twelve) (guard : d1865 pattern = 1) : d1502 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7326 (pattern : Twelve) (guard : d1865 pattern = 1) : d1514 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7325 pattern childGuard
    simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7327 (pattern : Twelve) (guard : d1865 pattern = 1) : d1529 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7326 pattern childGuard
    simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7328 (pattern : Twelve) (guard : d1865 pattern = 1) : d1539 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7324 pattern childGuard
    simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7327 pattern childGuard
    simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7329 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (0 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7278 pattern childGuard
    simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7330 (pattern : Twelve) (guard : d1865 pattern = 1) : d1503 pattern ≤ (0 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7296 pattern childGuard
    simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7331 (pattern : Twelve) (guard : d1865 pattern = 1) : d1515 pattern ≤ (0 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7329 pattern childGuard
    simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7330 pattern childGuard
    simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7332 (pattern : Twelve) (guard : d1865 pattern = 1) : d1530 pattern ≤ (0 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7215 pattern childGuard
    simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7331 pattern childGuard
    simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7333 (pattern : Twelve) (guard : d1865 pattern = 1) : d1504 pattern ≤ (0 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7334 (pattern : Twelve) (guard : d1865 pattern = 1) : d1516 pattern ≤ (0 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7333 pattern childGuard
    simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7171 pattern childGuard
    simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7335 (pattern : Twelve) (guard : d1865 pattern = 1) : d1531 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7334 pattern childGuard
    simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7336 (pattern : Twelve) (guard : d1865 pattern = 1) : d1540 pattern ≤ (0 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7332 pattern childGuard
    simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7335 pattern childGuard
    simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7337 (pattern : Twelve) (guard : d1865 pattern = 1) : d1546 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7328 pattern childGuard
    simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7336 pattern childGuard
    simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7338 (pattern : Twelve) (guard : d1865 pattern = 1) : d1547 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7320 pattern childGuard
    simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7339 (pattern : Twelve) (guard : d1865 pattern = 1) : d1550 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7337 pattern childGuard
    simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7338 pattern childGuard
    simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7340 (pattern : Twelve) (guard : d1865 pattern = 1) : d1553 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7321 pattern childGuard
    simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7339 pattern childGuard
    simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7341 (pattern : Twelve) (guard : d1865 pattern = 1) : d1556 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7309 pattern childGuard
    simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7340 pattern childGuard
    simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7342 (pattern : Twelve) (guard : d1865 pattern = 1) : d1753 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7343 (pattern : Twelve) (guard : d1865 pattern = 1) : d1754 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7344 (pattern : Twelve) (guard : d1865 pattern = 1) : d1763 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7342 pattern childGuard
    simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7343 pattern childGuard
    simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7345 (pattern : Twelve) (guard : d1865 pattern = 1) : d1745 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7346 (pattern : Twelve) (guard : d1865 pattern = 1) : d1746 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7347 (pattern : Twelve) (guard : d1865 pattern = 1) : d1749 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7345 pattern childGuard
    simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7346 pattern childGuard
    simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7348 (pattern : Twelve) (guard : d1865 pattern = 1) : d1755 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7283 pattern childGuard
    simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7347 pattern childGuard
    simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7349 (pattern : Twelve) (guard : d1865 pattern = 1) : d1764 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7348 pattern childGuard
    simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7301 pattern childGuard
    simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7350 (pattern : Twelve) (guard : d1865 pattern = 1) : d1770 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7344 pattern childGuard
    simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7349 pattern childGuard
    simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7351 (pattern : Twelve) (guard : d1865 pattern = 1) : d1756 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7345 pattern childGuard
    simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7352 (pattern : Twelve) (guard : d1865 pattern = 1) : d1757 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7216 pattern childGuard
    simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7353 (pattern : Twelve) (guard : d1865 pattern = 1) : d1765 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7351 pattern childGuard
    simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7352 pattern childGuard
    simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7354 (pattern : Twelve) (guard : d1865 pattern = 1) : d1747 pattern ≤ (0 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7355 (pattern : Twelve) (guard : d1865 pattern = 1) : d1750 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7354 pattern childGuard
    simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7171 pattern childGuard
    simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7356 (pattern : Twelve) (guard : d1865 pattern = 1) : d1758 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7300 pattern childGuard
    simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7355 pattern childGuard
    simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7357 (pattern : Twelve) (guard : d1865 pattern = 1) : d1759 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7217 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7358 (pattern : Twelve) (guard : d1865 pattern = 1) : d1766 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7356 pattern childGuard
    simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7357 pattern childGuard
    simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7359 (pattern : Twelve) (guard : d1865 pattern = 1) : d1771 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7353 pattern childGuard
    simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7358 pattern childGuard
    simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7360 (pattern : Twelve) (guard : d1865 pattern = 1) : d1772 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7349 pattern childGuard
    simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7361 (pattern : Twelve) (guard : d1865 pattern = 1) : d1775 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7359 pattern childGuard
    simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7360 pattern childGuard
    simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7362 (pattern : Twelve) (guard : d1865 pattern = 1) : d1777 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1777, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7350 pattern childGuard
    simpa only [d1777, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1777, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7361 pattern childGuard
    simpa only [d1777, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7363 (pattern : Twelve) (guard : d1865 pattern = 1) : d1760 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1760, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1760, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1760, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7345 pattern childGuard
    simpa only [d1760, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7364 (pattern : Twelve) (guard : d1865 pattern = 1) : d1767 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1767, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7363 pattern childGuard
    simpa only [d1767, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1767, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7343 pattern childGuard
    simpa only [d1767, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7365 (pattern : Twelve) (guard : d1865 pattern = 1) : d1773 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1773, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7364 pattern childGuard
    simpa only [d1773, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1773, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7349 pattern childGuard
    simpa only [d1773, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7366 (pattern : Twelve) (guard : d1865 pattern = 1) : d1748 pattern ≤ (0 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1748, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7311 pattern childGuard
    simpa only [d1748, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1748, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1748, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7367 (pattern : Twelve) (guard : d1865 pattern = 1) : d1751 pattern ≤ (0 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1751, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7345 pattern childGuard
    simpa only [d1751, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1751, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7366 pattern childGuard
    simpa only [d1751, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7368 (pattern : Twelve) (guard : d1865 pattern = 1) : d1761 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1761, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1761, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1761, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7367 pattern childGuard
    simpa only [d1761, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7369 (pattern : Twelve) (guard : d1865 pattern = 1) : d1768 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1768, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7368 pattern childGuard
    simpa only [d1768, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1768, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7301 pattern childGuard
    simpa only [d1768, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7370 (pattern : Twelve) (guard : d1865 pattern = 1) : d1752 pattern ≤ (0 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1752, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7171 pattern childGuard
    simpa only [d1752, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1752, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3235 pattern childGuard
    simpa only [d1752, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7371 (pattern : Twelve) (guard : d1865 pattern = 1) : d1762 pattern ≤ (0 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1762, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7300 pattern childGuard
    simpa only [d1762, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1762, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7370 pattern childGuard
    simpa only [d1762, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7372 (pattern : Twelve) (guard : d1865 pattern = 1) : d191 pattern ≤ (0 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7217 pattern childGuard
    simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d191, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7373 (pattern : Twelve) (guard : d1865 pattern = 1) : d202 pattern ≤ (0 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7372 pattern childGuard
    simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d202, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7374 (pattern : Twelve) (guard : d1865 pattern = 1) : d1769 pattern ≤ (0 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1769, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7371 pattern childGuard
    simpa only [d1769, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1769, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7373 pattern childGuard
    simpa only [d1769, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7375 (pattern : Twelve) (guard : d1865 pattern = 1) : d1774 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1774, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7369 pattern childGuard
    simpa only [d1774, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1774, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7374 pattern childGuard
    simpa only [d1774, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7376 (pattern : Twelve) (guard : d1865 pattern = 1) : d1776 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1776, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7375 pattern childGuard
    simpa only [d1776, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1776, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7360 pattern childGuard
    simpa only [d1776, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7377 (pattern : Twelve) (guard : d1865 pattern = 1) : d1778 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1778, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7365 pattern childGuard
    simpa only [d1778, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1778, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7376 pattern childGuard
    simpa only [d1778, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7378 (pattern : Twelve) (guard : d1865 pattern = 1) : d1779 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1779, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7362 pattern childGuard
    simpa only [d1779, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1779, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7377 pattern childGuard
    simpa only [d1779, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7379 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7380 (pattern : Twelve) (guard : d1867 pattern = 1) : d477 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7379 pattern childGuard
    simpa only [d1867, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7381 (pattern : Twelve) (guard : d1867 pattern = 1) : d498 pattern ≤ (0 : Int) + d646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d498, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d498, d646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d498, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7380 pattern childGuard
    simpa only [d498, d646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7382 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7383 (pattern : Twelve) (guard : d1867 pattern = 1) : d478 pattern ≤ (0 : Int) + d634 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d478, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d1867, d478, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d478, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7382 pattern childGuard
    simpa only [d1867, d478, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7384 (pattern : Twelve) (guard : d1867 pattern = 1) : d499 pattern ≤ (0 : Int) + d647 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d499, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d499, d647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d499, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7383 pattern childGuard
    simpa only [d499, d647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7385 (pattern : Twelve) (guard : d1867 pattern = 1) : d532 pattern ≤ (0 : Int) + d680 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d532, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7381 pattern childGuard
    simpa only [d532, d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d532, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7384 pattern childGuard
    simpa only [d532, d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7386 (pattern : Twelve) (guard : d1867 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  omega
theorem c7387 (pattern : Twelve) (guard : d1867 pattern = 1) : d162 pattern ≤ (0 : Int) + d162 pattern := by
  omega
theorem c7388 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7389 (pattern : Twelve) (guard : d1867 pattern = 1) : d479 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7388 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7390 (pattern : Twelve) (guard : d1867 pattern = 1) : d500 pattern ≤ (0 : Int) + d648 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d500, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d500, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d500, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d500, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7391 (pattern : Twelve) (guard : d1867 pattern = 1) : d533 pattern ≤ (0 : Int) + d681 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d533, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7386 pattern childGuard
    simpa only [d533, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d533, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7390 pattern childGuard
    simpa only [d533, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7392 (pattern : Twelve) (guard : d1867 pattern = 1) : d561 pattern ≤ (0 : Int) + d709 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d561, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7385 pattern childGuard
    simpa only [d561, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d561, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7391 pattern childGuard
    simpa only [d561, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7393 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7394 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7393 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7395 (pattern : Twelve) (guard : d1867 pattern = 1) : d501 pattern ≤ (0 : Int) + d649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d501, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d501, d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d501, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d501, d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7396 (pattern : Twelve) (guard : d1867 pattern = 1) : d534 pattern ≤ (0 : Int) + d682 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d534, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7384 pattern childGuard
    simpa only [d534, d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d534, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7395 pattern childGuard
    simpa only [d534, d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7397 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7398 (pattern : Twelve) (guard : d1867 pattern = 1) : d481 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d481, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d1867, d481, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d481, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7397 pattern childGuard
    simpa only [d1867, d481, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7399 (pattern : Twelve) (guard : d1867 pattern = 1) : d502 pattern ≤ (0 : Int) + d650 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d502, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7387 pattern childGuard
    simpa only [d502, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d502, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7398 pattern childGuard
    simpa only [d502, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7400 (pattern : Twelve) (guard : d1867 pattern = 1) : d482 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d482, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3272 pattern childGuard
    simpa only [d1867, d482, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d482, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7388 pattern childGuard
    simpa only [d1867, d482, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7401 (pattern : Twelve) (guard : d1867 pattern = 1) : d503 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d503, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d503, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d503, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d503, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7402 (pattern : Twelve) (guard : d1867 pattern = 1) : d535 pattern ≤ (0 : Int) + d683 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d535, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7399 pattern childGuard
    simpa only [d535, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d535, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7401 pattern childGuard
    simpa only [d535, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7403 (pattern : Twelve) (guard : d1867 pattern = 1) : d562 pattern ≤ (0 : Int) + d710 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d562, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7396 pattern childGuard
    simpa only [d562, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d562, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7402 pattern childGuard
    simpa only [d562, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7404 (pattern : Twelve) (guard : d1867 pattern = 1) : d588 pattern ≤ (0 : Int) + d736 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d588, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7392 pattern childGuard
    simpa only [d588, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d588, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7403 pattern childGuard
    simpa only [d588, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7405 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7406 (pattern : Twelve) (guard : d1867 pattern = 1) : d483 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7405 pattern childGuard
    simpa only [d1867, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7407 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7408 (pattern : Twelve) (guard : d1867 pattern = 1) : d484 pattern ≤ (0 : Int) + d637 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d484, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3284 pattern childGuard
    simpa only [d1867, d484, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d484, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7407 pattern childGuard
    simpa only [d1867, d484, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7409 (pattern : Twelve) (guard : d1867 pattern = 1) : d504 pattern ≤ (0 : Int) + d652 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d504, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7406 pattern childGuard
    simpa only [d504, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d504, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7408 pattern childGuard
    simpa only [d504, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7410 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7411 (pattern : Twelve) (guard : d1867 pattern = 1) : d485 pattern ≤ (0 : Int) + d638 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d485, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d1867, d485, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d485, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7410 pattern childGuard
    simpa only [d1867, d485, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7412 (pattern : Twelve) (guard : d1867 pattern = 1) : d486 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d486, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3289 pattern childGuard
    simpa only [d1867, d486, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d486, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7014 pattern childGuard
    simpa only [d1867, d486, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7413 (pattern : Twelve) (guard : d1867 pattern = 1) : d505 pattern ≤ (0 : Int) + d653 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d505, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7411 pattern childGuard
    simpa only [d505, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d505, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d505, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7414 (pattern : Twelve) (guard : d1867 pattern = 1) : d536 pattern ≤ (0 : Int) + d684 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d536, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7409 pattern childGuard
    simpa only [d536, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d536, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7413 pattern childGuard
    simpa only [d536, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7415 (pattern : Twelve) (guard : d1867 pattern = 1) : d487 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7397 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7416 (pattern : Twelve) (guard : d1867 pattern = 1) : d506 pattern ≤ (0 : Int) + d654 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d506, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7411 pattern childGuard
    simpa only [d506, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d506, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d506, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7417 (pattern : Twelve) (guard : d1867 pattern = 1) : d170 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3696 pattern childGuard
    simpa only [d1867, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1867, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7418 (pattern : Twelve) (guard : d1867 pattern = 1) : d507 pattern ≤ (0 : Int) + d655 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d507, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d507, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d507, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7417 pattern childGuard
    simpa only [d507, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7419 (pattern : Twelve) (guard : d1867 pattern = 1) : d537 pattern ≤ (0 : Int) + d685 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d537, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7416 pattern childGuard
    simpa only [d537, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d537, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7418 pattern childGuard
    simpa only [d537, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
