/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons036
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5180 (pattern : Twelve) (guard : d1849 pattern = 1) : d1446 pattern ≤ (0 : Int) + d1383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1446, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d1849, d1446, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1446, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d1849, d1446, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5181 (pattern : Twelve) (guard : d1849 pattern = 1) : d1451 pattern ≤ (0 : Int) + d1390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1451, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5121 pattern childGuard
    simpa only [d1451, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1451, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5180 pattern childGuard
    simpa only [d1451, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5182 (pattern : Twelve) (guard : d1849 pattern = 1) : d42 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5183 (pattern : Twelve) (guard : d1849 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1452, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5182 pattern childGuard
    simpa only [d1452, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1452, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1452, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5184 (pattern : Twelve) (guard : d1849 pattern = 1) : d1457 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1457, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5181 pattern childGuard
    simpa only [d1457, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1457, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5183 pattern childGuard
    simpa only [d1457, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5185 (pattern : Twelve) (guard : d1849 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1460, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1460, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1460, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5184 pattern childGuard
    simpa only [d1460, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5186 (pattern : Twelve) (guard : d1849 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1461, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1461, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1461, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1461, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5187 (pattern : Twelve) (guard : d1849 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1464, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5185 pattern childGuard
    simpa only [d1464, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1464, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5186 pattern childGuard
    simpa only [d1464, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5188 (pattern : Twelve) (guard : d1849 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1405 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1466, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5177 pattern childGuard
    simpa only [d1466, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1466, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5187 pattern childGuard
    simpa only [d1466, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5189 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d29, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5190 (pattern : Twelve) (guard : d1849 pattern = 1) : d29 pattern ≤ (0 : Int) + d1384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5189 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5191 (pattern : Twelve) (guard : d1849 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5190 pattern childGuard
    simpa only [d1449, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1449, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5192 (pattern : Twelve) (guard : d1849 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1397 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5174 pattern childGuard
    simpa only [d1456, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5191 pattern childGuard
    simpa only [d1456, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5193 (pattern : Twelve) (guard : d1849 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1402 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5192 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5194 (pattern : Twelve) (guard : d1849 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1467, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5193 pattern childGuard
    simpa only [d1467, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1467, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5187 pattern childGuard
    simpa only [d1467, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5195 (pattern : Twelve) (guard : d1849 pattern = 1) : d1469 pattern ≤ (0 : Int) + d1408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1469, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5188 pattern childGuard
    simpa only [d1469, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1469, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5194 pattern childGuard
    simpa only [d1469, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5196 (pattern : Twelve) (guard : d1849 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1467, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d1467, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1467, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5187 pattern childGuard
    simpa only [d1467, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5197 (pattern : Twelve) (guard : d1849 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5196 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5194 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5198 (pattern : Twelve) (guard : d1849 pattern = 1) : d1470 pattern ≤ (0 : Int) + d1410 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1470, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5195 pattern childGuard
    simpa only [d1470, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1470, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5197 pattern childGuard
    simpa only [d1470, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5199 (pattern : Twelve) (guard : d0 pattern = 1) : d1331 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5200 (pattern : Twelve) (guard : d1849 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1337, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d1849, d1337, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1337, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5199 pattern childGuard
    simpa only [d1849, d1337, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5201 (pattern : Twelve) (guard : d1849 pattern = 1) : d1453 pattern ≤ (0 : Int) + d1390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1453, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5121 pattern childGuard
    simpa only [d1453, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1453, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5200 pattern childGuard
    simpa only [d1453, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5202 (pattern : Twelve) (guard : d1849 pattern = 1) : d1447 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1447, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1849, d1447, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1447, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1849, d1447, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5203 (pattern : Twelve) (guard : d1849 pattern = 1) : d1454 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1454, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5202 pattern childGuard
    simpa only [d1454, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1454, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1454, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5204 (pattern : Twelve) (guard : d1849 pattern = 1) : d1458 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1458, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5201 pattern childGuard
    simpa only [d1458, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1458, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5203 pattern childGuard
    simpa only [d1458, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5205 (pattern : Twelve) (guard : d1849 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1462, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1462, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1462, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5204 pattern childGuard
    simpa only [d1462, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5206 (pattern : Twelve) (guard : d1849 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1465, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5205 pattern childGuard
    simpa only [d1465, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1465, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5186 pattern childGuard
    simpa only [d1465, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5207 (pattern : Twelve) (guard : d1849 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1468, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d1468, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1468, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5206 pattern childGuard
    simpa only [d1468, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5208 (pattern : Twelve) (guard : d1849 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1468, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5193 pattern childGuard
    simpa only [d1468, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1468, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5206 pattern childGuard
    simpa only [d1468, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5209 (pattern : Twelve) (guard : d1849 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5207 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5208 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5210 (pattern : Twelve) (guard : d1849 pattern = 1) : d1471 pattern ≤ (0 : Int) + d1411 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1471, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5198 pattern childGuard
    simpa only [d1471, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1471, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5209 pattern childGuard
    simpa only [d1471, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5211 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5212 (pattern : Twelve) (guard : d1849 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5211 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5213 (pattern : Twelve) (guard : d1849 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1693 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1716, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5163 pattern childGuard
    simpa only [d1716, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1716, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5212 pattern childGuard
    simpa only [d1716, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5214 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5215 (pattern : Twelve) (guard : d1849 pattern = 1) : d42 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5216 (pattern : Twelve) (guard : d1849 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1694 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1452, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5215 pattern childGuard
    simpa only [d1452, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1452, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1452, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5217 (pattern : Twelve) (guard : d1849 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1697 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1719, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5213 pattern childGuard
    simpa only [d1719, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1719, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5216 pattern childGuard
    simpa only [d1719, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5218 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5219 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d1848, d1645, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5220 (pattern : Twelve) (guard : d1849 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5221 (pattern : Twelve) (guard : d1849 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1716, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5170 pattern childGuard
    simpa only [d1716, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1716, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5220 pattern childGuard
    simpa only [d1716, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5222 (pattern : Twelve) (guard : d1849 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1719, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5221 pattern childGuard
    simpa only [d1719, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1719, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5183 pattern childGuard
    simpa only [d1719, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5223 (pattern : Twelve) (guard : d1849 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1700 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5217 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5222 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5224 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5225 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (0 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1536 pattern childGuard
    simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5226 (pattern : Twelve) (guard : d1849 pattern = 1) : d128 pattern ≤ (0 : Int) + d1692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5227 (pattern : Twelve) (guard : d1849 pattern = 1) : d1717 pattern ≤ (0 : Int) + d1696 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1717, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5182 pattern childGuard
    simpa only [d1717, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1717, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5226 pattern childGuard
    simpa only [d1717, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5228 (pattern : Twelve) (guard : d1849 pattern = 1) : d822 pattern ≤ (0 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1541 pattern childGuard
    simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c279 pattern childGuard
    simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5229 (pattern : Twelve) (guard : d1849 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5228 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5230 (pattern : Twelve) (guard : d1849 pattern = 1) : d1720 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1720, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5227 pattern childGuard
    simpa only [d1720, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1720, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5229 pattern childGuard
    simpa only [d1720, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5231 (pattern : Twelve) (guard : d1849 pattern = 1) : d1722 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1722, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5222 pattern childGuard
    simpa only [d1722, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1722, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5230 pattern childGuard
    simpa only [d1722, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5232 (pattern : Twelve) (guard : d1849 pattern = 1) : d1723 pattern ≤ (0 : Int) + d1702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1723, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5222 pattern childGuard
    simpa only [d1723, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1723, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1723, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5233 (pattern : Twelve) (guard : d1849 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1725, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5231 pattern childGuard
    simpa only [d1725, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1725, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5232 pattern childGuard
    simpa only [d1725, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5234 (pattern : Twelve) (guard : d1849 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1727, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5223 pattern childGuard
    simpa only [d1727, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1727, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5233 pattern childGuard
    simpa only [d1727, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5235 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5236 (pattern : Twelve) (guard : d1849 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1667, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d1849, d1667, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1667, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5235 pattern childGuard
    simpa only [d1849, d1667, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5237 (pattern : Twelve) (guard : d1849 pattern = 1) : d1718 pattern ≤ (0 : Int) + d1696 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1718, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5182 pattern childGuard
    simpa only [d1718, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1718, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5236 pattern childGuard
    simpa only [d1718, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5238 (pattern : Twelve) (guard : d1849 pattern = 1) : d1721 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1721, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5237 pattern childGuard
    simpa only [d1721, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1721, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1552 pattern childGuard
    simpa only [d1721, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5239 (pattern : Twelve) (guard : d1849 pattern = 1) : d1724 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1724, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5222 pattern childGuard
    simpa only [d1724, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1724, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5238 pattern childGuard
    simpa only [d1724, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5240 (pattern : Twelve) (guard : d1849 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1726, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5239 pattern childGuard
    simpa only [d1726, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1726, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5232 pattern childGuard
    simpa only [d1726, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5241 (pattern : Twelve) (guard : d1849 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1728, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5223 pattern childGuard
    simpa only [d1728, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1728, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5240 pattern childGuard
    simpa only [d1728, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5242 (pattern : Twelve) (guard : d1849 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5234 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5241 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5243 (pattern : Twelve) (guard : d1848 pattern = 1) : d184 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4958 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4966 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5244 (pattern : Twelve) (guard : d0 pattern = 1) : d372 pattern ≤ (0 : Int) + d185 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5245 (pattern : Twelve) (guard : d1870 pattern = 1) : d389 pattern ≤ (0 : Int) + d425 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d389, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5243 pattern childGuard
    simpa only [d1870, d389, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d389, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5244 pattern childGuard
    simpa only [d1870, d389, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5246 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5247 (pattern : Twelve) (guard : d1848 pattern = 1) : d367 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5246 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5248 (pattern : Twelve) (guard : d1848 pattern = 1) : d373 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4966 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5247 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5249 (pattern : Twelve) (guard : d0 pattern = 1) : d374 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5250 (pattern : Twelve) (guard : d1870 pattern = 1) : d390 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d390, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d1870, d390, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d390, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5249 pattern childGuard
    simpa only [d1870, d390, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5251 (pattern : Twelve) (guard : d1870 pattern = 1) : d402 pattern ≤ (0 : Int) + d444 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d402, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5245 pattern childGuard
    simpa only [d402, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d402, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5250 pattern childGuard
    simpa only [d402, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5252 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5253 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5252 pattern childGuard
    simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5254 (pattern : Twelve) (guard : d1848 pattern = 1) : d375 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4975 pattern childGuard
    simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5253 pattern childGuard
    simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5255 (pattern : Twelve) (guard : d0 pattern = 1) : d376 pattern ≤ (0 : Int) + d188 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5256 (pattern : Twelve) (guard : d1870 pattern = 1) : d391 pattern ≤ (0 : Int) + d427 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d391, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5254 pattern childGuard
    simpa only [d1870, d391, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d391, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5255 pattern childGuard
    simpa only [d1870, d391, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5257 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5258 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5257 pattern childGuard
    simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5259 (pattern : Twelve) (guard : d0 pattern = 1) : d378 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5260 (pattern : Twelve) (guard : d1870 pattern = 1) : d392 pattern ≤ (0 : Int) + d428 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d392, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5258 pattern childGuard
    simpa only [d1870, d392, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d392, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5259 pattern childGuard
    simpa only [d1870, d392, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5261 (pattern : Twelve) (guard : d1870 pattern = 1) : d403 pattern ≤ (0 : Int) + d445 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d403, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5256 pattern childGuard
    simpa only [d403, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d403, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5260 pattern childGuard
    simpa only [d403, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5262 (pattern : Twelve) (guard : d1870 pattern = 1) : d409 pattern ≤ (0 : Int) + d455 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d409, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5251 pattern childGuard
    simpa only [d409, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d409, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5261 pattern childGuard
    simpa only [d409, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5263 (pattern : Twelve) (guard : d1848 pattern = 1) : d375 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4991 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4998 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5264 (pattern : Twelve) (guard : d1870 pattern = 1) : d391 pattern ≤ (0 : Int) + d429 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d391, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5263 pattern childGuard
    simpa only [d1870, d391, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d391, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5255 pattern childGuard
    simpa only [d1870, d391, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5265 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4998 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5266 (pattern : Twelve) (guard : d1870 pattern = 1) : d392 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d392, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d1870, d392, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d392, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5259 pattern childGuard
    simpa only [d1870, d392, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5267 (pattern : Twelve) (guard : d1870 pattern = 1) : d403 pattern ≤ (0 : Int) + d446 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d403, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5264 pattern childGuard
    simpa only [d403, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d403, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5266 pattern childGuard
    simpa only [d403, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5268 (pattern : Twelve) (guard : d1848 pattern = 1) : d379 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5003 pattern childGuard
    simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5269 (pattern : Twelve) (guard : d0 pattern = 1) : d380 pattern ≤ (0 : Int) + d191 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5270 (pattern : Twelve) (guard : d1870 pattern = 1) : d393 pattern ≤ (0 : Int) + d431 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d393, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5268 pattern childGuard
    simpa only [d1870, d393, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d393, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5269 pattern childGuard
    simpa only [d1870, d393, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5271 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5272 (pattern : Twelve) (guard : d0 pattern = 1) : d378 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5273 (pattern : Twelve) (guard : d1870 pattern = 1) : d394 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d394, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1870, d394, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d394, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5272 pattern childGuard
    simpa only [d1870, d394, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5274 (pattern : Twelve) (guard : d1870 pattern = 1) : d404 pattern ≤ (0 : Int) + d447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d404, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5270 pattern childGuard
    simpa only [d404, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d404, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d404, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5275 (pattern : Twelve) (guard : d1870 pattern = 1) : d410 pattern ≤ (0 : Int) + d456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d410, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5267 pattern childGuard
    simpa only [d410, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d410, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5274 pattern childGuard
    simpa only [d410, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5276 (pattern : Twelve) (guard : d1870 pattern = 1) : d415 pattern ≤ (0 : Int) + d465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d415, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5262 pattern childGuard
    simpa only [d415, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d415, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5275 pattern childGuard
    simpa only [d415, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5277 (pattern : Twelve) (guard : d1848 pattern = 1) : d381 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5015 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5278 (pattern : Twelve) (guard : d0 pattern = 1) : d382 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5279 (pattern : Twelve) (guard : d1870 pattern = 1) : d395 pattern ≤ (0 : Int) + d433 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d395, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5277 pattern childGuard
    simpa only [d1870, d395, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d395, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5278 pattern childGuard
    simpa only [d1870, d395, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5280 (pattern : Twelve) (guard : d1848 pattern = 1) : d383 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5281 (pattern : Twelve) (guard : d0 pattern = 1) : d378 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5282 (pattern : Twelve) (guard : d1870 pattern = 1) : d396 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d396, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d1870, d396, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d396, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5281 pattern childGuard
    simpa only [d1870, d396, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5283 (pattern : Twelve) (guard : d1870 pattern = 1) : d405 pattern ≤ (0 : Int) + d448 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d405, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5279 pattern childGuard
    simpa only [d405, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d405, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5282 pattern childGuard
    simpa only [d405, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5284 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2581 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5285 (pattern : Twelve) (guard : d0 pattern = 1) : d384 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5286 (pattern : Twelve) (guard : d1870 pattern = 1) : d397 pattern ≤ (0 : Int) + d435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d397, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d397, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d397, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5285 pattern childGuard
    simpa only [d1870, d397, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5287 (pattern : Twelve) (guard : d0 pattern = 1) : d385 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5288 (pattern : Twelve) (guard : d1870 pattern = 1) : d398 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d398, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d398, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d398, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5287 pattern childGuard
    simpa only [d1870, d398, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5289 (pattern : Twelve) (guard : d1870 pattern = 1) : d406 pattern ≤ (0 : Int) + d449 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5286 pattern childGuard
    simpa only [d406, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5288 pattern childGuard
    simpa only [d406, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5290 (pattern : Twelve) (guard : d1870 pattern = 1) : d411 pattern ≤ (0 : Int) + d457 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d411, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5283 pattern childGuard
    simpa only [d411, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d411, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5289 pattern childGuard
    simpa only [d411, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5291 (pattern : Twelve) (guard : d0 pattern = 1) : d380 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5292 (pattern : Twelve) (guard : d1870 pattern = 1) : d399 pattern ≤ (0 : Int) + d437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d399, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1870, d399, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d399, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5291 pattern childGuard
    simpa only [d1870, d399, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5293 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d450 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5292 pattern childGuard
    simpa only [d407, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d407, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5294 (pattern : Twelve) (guard : d1870 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c5295 (pattern : Twelve) (guard : d1870 pattern = 1) : d412 pattern ≤ (0 : Int) + d458 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d412, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5293 pattern childGuard
    simpa only [d412, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d412, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d412, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5296 (pattern : Twelve) (guard : d1870 pattern = 1) : d416 pattern ≤ (0 : Int) + d466 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d416, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5290 pattern childGuard
    simpa only [d416, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d416, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5295 pattern childGuard
    simpa only [d416, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5297 (pattern : Twelve) (guard : d1870 pattern = 1) : d419 pattern ≤ (0 : Int) + d471 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d419, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5276 pattern childGuard
    simpa only [d419, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d419, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5296 pattern childGuard
    simpa only [d419, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5298 (pattern : Twelve) (guard : d0 pattern = 1) : d380 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5299 (pattern : Twelve) (guard : d1870 pattern = 1) : d399 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d399, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1870, d399, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d399, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5298 pattern childGuard
    simpa only [d1870, d399, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5300 (pattern : Twelve) (guard : d1870 pattern = 1) : d394 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d394, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1870, d394, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d394, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5272 pattern childGuard
    simpa only [d1870, d394, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5301 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5299 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5300 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5302 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5303 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5302 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5304 (pattern : Twelve) (guard : d1870 pattern = 1) : d399 pattern ≤ (0 : Int) + d439 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d399, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d1870, d399, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d399, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5298 pattern childGuard
    simpa only [d1870, d399, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5305 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5257 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5306 (pattern : Twelve) (guard : d1870 pattern = 1) : d394 pattern ≤ (0 : Int) + d440 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d394, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5305 pattern childGuard
    simpa only [d1870, d394, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d394, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5272 pattern childGuard
    simpa only [d1870, d394, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5307 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d451 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5304 pattern childGuard
    simpa only [d407, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5306 pattern childGuard
    simpa only [d407, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5308 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5301 pattern childGuard
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5307 pattern childGuard
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5309 (pattern : Twelve) (guard : d1870 pattern = 1) : d399 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d399, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1870, d399, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d399, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5298 pattern childGuard
    simpa only [d1870, d399, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5310 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5309 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5311 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5301 pattern childGuard
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5310 pattern childGuard
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5312 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5308 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5311 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5313 (pattern : Twelve) (guard : d1870 pattern = 1) : d399 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d399, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1870, d399, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d399, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5298 pattern childGuard
    simpa only [d1870, d399, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5314 (pattern : Twelve) (guard : d1870 pattern = 1) : d394 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d394, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1870, d394, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d394, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5272 pattern childGuard
    simpa only [d1870, d394, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5315 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5313 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5314 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5316 (pattern : Twelve) (guard : d0 pattern = 1) : d384 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5317 (pattern : Twelve) (guard : d1870 pattern = 1) : d397 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d397, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d397, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d397, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5316 pattern childGuard
    simpa only [d1870, d397, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5318 (pattern : Twelve) (guard : d1870 pattern = 1) : d406 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5317 pattern childGuard
    simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5288 pattern childGuard
    simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5319 (pattern : Twelve) (guard : d1870 pattern = 1) : d413 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d413, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5315 pattern childGuard
    simpa only [d413, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d413, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5318 pattern childGuard
    simpa only [d413, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
