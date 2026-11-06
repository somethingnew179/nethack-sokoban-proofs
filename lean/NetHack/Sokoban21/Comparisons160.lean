/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons159
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22400 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (19 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22309 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22342 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22401 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (19 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22394 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22400 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22402 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (19 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22118 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22401 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22403 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (19 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22146 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22094 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22404 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (19 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22246 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22110 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22405 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (19 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22403 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22404 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22406 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (19 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22407 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (19 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22406 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22408 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (19 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22407 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22391 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22409 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (19 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22402 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22408 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22410 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (19 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22327 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22411 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (19 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22257 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22166 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22412 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (19 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22411 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22413 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (19 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22410 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22412 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22414 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (19 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22164 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22413 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22415 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (19 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22128 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22255 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22416 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (19 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22417 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (19 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22415 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22416 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22418 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22322 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22419 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (19 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22417 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22418 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22420 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (19 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22414 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22419 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22421 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (19 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22409 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22420 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22422 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (19 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22398 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22423 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (19 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22421 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22422 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22424 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (19 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22399 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22423 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22425 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (19 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22327 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22426 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (19 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22344 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22427 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (19 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22425 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22426 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22428 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (19 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22427 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22429 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (19 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22128 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22156 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22430 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (19 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22429 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22351 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22431 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (19 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22428 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22430 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22432 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (19 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22431 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22378 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22433 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (19 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22248 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22262 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22434 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (19 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22343 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22433 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22435 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (19 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22157 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22434 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22436 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (19 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22435 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22377 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22437 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (19 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22342 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22438 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (19 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22262 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22439 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (19 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22437 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22438 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22440 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (19 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22292 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22439 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22441 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22350 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22442 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (19 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22297 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22441 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22443 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (19 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22440 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22442 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22444 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (19 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22436 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22443 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22445 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (19 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22378 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22446 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (19 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22444 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22445 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22447 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (19 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22432 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22446 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22448 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (19 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22424 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22447 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22449 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (19 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22383 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22448 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22450 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (19 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22088 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22092 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22451 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (19 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22450 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22452 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (19 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22451 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22453 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (19 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22452 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22454 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (19 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22100 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22455 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (19 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22453 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22454 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22456 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (19 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22095 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22404 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22457 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22450 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22456 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22458 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (19 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22459 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (19 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22457 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22458 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22460 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (19 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22333 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22459 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22461 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (19 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22100 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22171 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22462 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (19 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22461 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22102 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22463 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (19 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22462 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22464 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (19 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22460 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22463 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22465 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (19 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22455 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22464 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22466 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22467 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22457 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22466 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22468 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (19 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22467 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22469 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (19 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22461 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22470 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (19 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22468 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22469 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22471 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (19 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22166 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22119 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22472 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (19 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22456 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22471 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22473 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (19 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22472 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22416 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22474 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (19 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22348 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22473 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22475 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (19 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22171 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22120 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22476 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (19 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22475 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22172 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22477 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (19 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22476 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22478 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (19 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22474 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22477 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22479 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (19 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22470 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22478 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22480 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (19 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22464 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22481 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (19 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22479 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22480 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22482 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (19 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22465 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22481 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22483 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (19 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22100 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22128 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22484 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (19 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22483 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22485 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (19 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22453 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22484 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22486 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (19 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22461 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22188 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22487 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (19 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22486 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22488 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (19 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22460 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22487 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22489 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (19 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22485 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22488 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22490 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (19 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22461 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22168 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22491 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (19 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22490 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22492 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (19 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22468 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22491 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22493 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (19 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22475 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22214 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22494 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (19 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22493 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22495 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (19 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22474 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22494 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22496 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (19 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22492 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22495 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22497 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (19 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22488 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22498 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (19 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22496 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22497 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22499 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (19 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22489 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22498 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22500 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (19 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22482 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22499 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22501 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (19 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22099 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22169 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22502 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22450 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22501 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22503 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22501 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22504 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22502 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22503 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22505 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (19 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22504 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22506 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (19 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22505 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22454 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22507 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (19 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22450 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22508 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (19 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22507 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22458 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22509 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (19 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22333 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22508 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22510 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (19 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22509 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22463 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22511 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (19 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22506 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22510 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22512 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (19 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22385 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22471 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22513 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (19 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22507 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22512 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22514 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (19 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22129 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22513 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22515 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (19 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22100 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22516 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (19 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22461 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22515 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22517 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (19 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22516 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22518 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (19 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22514 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22517 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22519 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (19 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22456 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22520 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (19 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22471 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22521 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (19 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22519 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22520 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22522 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (19 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22348 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22521 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22523 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (19 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22171 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22124 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22524 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (19 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22523 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22267 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22525 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (19 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22524 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22526 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (19 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22522 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22525 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22527 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (19 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22518 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22526 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22528 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (19 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22510 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22529 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (19 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22527 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22528 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22530 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (19 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22511 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22529 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22531 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (19 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22456 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22532 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (19 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22531 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22533 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (19 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22128 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22532 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22534 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (19 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22171 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22167 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22535 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (19 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22534 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22536 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (19 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22533 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22535 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22537 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (19 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22536 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22495 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22538 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (19 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22405 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22255 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22539 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (19 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22472 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22538 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
