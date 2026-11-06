/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons166
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c23380 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (20 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23376 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23379 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23381 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (20 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23372 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23382 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (20 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23380 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23381 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23383 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (20 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23373 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23382 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23384 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (20 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23366 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23383 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23385 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (20 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22983 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23053 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23386 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23334 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23385 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23387 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23385 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23388 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23386 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23387 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23389 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (20 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23388 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23390 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (20 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23389 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23338 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23391 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23334 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23392 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (20 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23391 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23342 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23393 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (20 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23217 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23392 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23394 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (20 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23393 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23347 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23395 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (20 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23390 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23394 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23396 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (20 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23355 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23397 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (20 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23391 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23396 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23398 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (20 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23397 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23399 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (20 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22984 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23400 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (20 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23345 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23399 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23401 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (20 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23400 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23402 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (20 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23398 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23401 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23403 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (20 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23340 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23404 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (20 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23355 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23405 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (20 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23403 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23404 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23406 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (20 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23232 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23405 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23407 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23408 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (20 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23407 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23151 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23409 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (20 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23408 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23410 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (20 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23406 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23409 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23411 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (20 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23402 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23410 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23412 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (20 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23394 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23413 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (20 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23411 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23412 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23414 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (20 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23395 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23413 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23415 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (20 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23340 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23416 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (20 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23415 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23417 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (20 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23416 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23418 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (20 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23051 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23419 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (20 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23418 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23420 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (20 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23417 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23419 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23421 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (20 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23420 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23379 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23422 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (20 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23139 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23423 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (20 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23356 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23422 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23424 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (20 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23423 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23425 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (20 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23424 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23378 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23426 (pattern : Twelve) (guard : d1 pattern = 1) : d182 pattern ≤ (20 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23139 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23427 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (20 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23404 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23426 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23428 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (20 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23098 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23427 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23429 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23325 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23430 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (20 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23428 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23429 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23431 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (20 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23425 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23430 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23432 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (20 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23379 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23433 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (20 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23431 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23432 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23434 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (20 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23421 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23433 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23435 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (20 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23414 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23434 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23436 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (20 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23384 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23435 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23437 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23201 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23203 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23438 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23202 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23437 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23439 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23204 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23440 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23438 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23439 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23441 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23202 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23442 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23205 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23441 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23443 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23437 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23444 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23437 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23445 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23443 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23444 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23446 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23442 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23445 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23447 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23233 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23206 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23448 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23447 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23449 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23446 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23448 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23450 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23440 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23449 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23451 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23205 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23443 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23452 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23233 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23453 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23451 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23452 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23454 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23455 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23454 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23151 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23456 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23447 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23455 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23457 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23234 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23458 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23456 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23457 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23459 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23453 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23458 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23460 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23449 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23461 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23459 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23460 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23462 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23450 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23461 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23463 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23202 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23443 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23464 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23463 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23439 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23465 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23464 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23449 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23466 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23437 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23467 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23443 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23466 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23468 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23205 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23467 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23469 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23468 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23448 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23470 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23471 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23151 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23470 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23472 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23447 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23471 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23473 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23472 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23429 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23474 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23469 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23473 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23475 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23474 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23460 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23476 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23465 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23475 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23477 (pattern : Twelve) (guard : d1 pattern = 1) : d1814 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23204 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23478 (pattern : Twelve) (guard : d1 pattern = 1) : d1815 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23479 (pattern : Twelve) (guard : d1 pattern = 1) : d1818 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23477 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23478 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23480 (pattern : Twelve) (guard : d1 pattern = 1) : d1821 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23479 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23458 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23481 (pattern : Twelve) (guard : d1 pattern = 1) : d1816 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23233 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23454 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23482 (pattern : Twelve) (guard : d1 pattern = 1) : d1819 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23481 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23457 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23483 (pattern : Twelve) (guard : d1 pattern = 1) : d1817 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23234 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23470 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23484 (pattern : Twelve) (guard : d1 pattern = 1) : d1820 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23483 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23485 (pattern : Twelve) (guard : d1 pattern = 1) : d1822 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23482 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23484 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23486 (pattern : Twelve) (guard : d1 pattern = 1) : d1823 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23458 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23487 (pattern : Twelve) (guard : d1 pattern = 1) : d1824 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23485 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23486 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23488 (pattern : Twelve) (guard : d1 pattern = 1) : d1825 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23480 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23487 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23489 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23476 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23488 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23490 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23462 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23489 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
