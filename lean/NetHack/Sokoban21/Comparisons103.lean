/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons102
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14420 (pattern : Twelve) (guard : d2301 pattern = 1) : d1345 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1345, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14419 pattern childGuard
    simpa only [d1345, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1345, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14381 pattern childGuard
    simpa only [d1345, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14421 (pattern : Twelve) (guard : d26 pattern = 1) : d1327 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14376 pattern childGuard
    simpa only [d26, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d26, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14422 (pattern : Twelve) (guard : d2301 pattern = 1) : d1334 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14421 pattern childGuard
    simpa only [d2301, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14384 pattern childGuard
    simpa only [d2301, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14423 (pattern : Twelve) (guard : d2301 pattern = 1) : d1340 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1340, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14302 pattern childGuard
    simpa only [d1340, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1340, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14422 pattern childGuard
    simpa only [d1340, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14424 (pattern : Twelve) (guard : d2301 pattern = 1) : d1346 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1346, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14423 pattern childGuard
    simpa only [d1346, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1346, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14390 pattern childGuard
    simpa only [d1346, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14425 (pattern : Twelve) (guard : d2301 pattern = 1) : d1349 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14420 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14424 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14426 (pattern : Twelve) (guard : d0 pattern = 1) : d1328 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14427 (pattern : Twelve) (guard : d2301 pattern = 1) : d1335 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14421 pattern childGuard
    simpa only [d2301, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14426 pattern childGuard
    simpa only [d2301, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14428 (pattern : Twelve) (guard : d2301 pattern = 1) : d1341 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1341, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14310 pattern childGuard
    simpa only [d1341, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1341, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14427 pattern childGuard
    simpa only [d1341, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14429 (pattern : Twelve) (guard : d0 pattern = 1) : d1329 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14430 (pattern : Twelve) (guard : d2301 pattern = 1) : d1336 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14388 pattern childGuard
    simpa only [d2301, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14429 pattern childGuard
    simpa only [d2301, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14431 (pattern : Twelve) (guard : d2301 pattern = 1) : d1342 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14430 pattern childGuard
    simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14432 (pattern : Twelve) (guard : d2301 pattern = 1) : d1347 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1347, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14428 pattern childGuard
    simpa only [d1347, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1347, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14431 pattern childGuard
    simpa only [d1347, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14433 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (2 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14434 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14357 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13468 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14435 (pattern : Twelve) (guard : d26 pattern = 1) : d1330 pattern ≤ (2 : Int) + d1277 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14433 pattern childGuard
    simpa only [d26, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14434 pattern childGuard
    simpa only [d26, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14436 (pattern : Twelve) (guard : d0 pattern = 1) : d1331 pattern ≤ (2 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14437 (pattern : Twelve) (guard : d2301 pattern = 1) : d1337 pattern ≤ (2 : Int) + d1277 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14435 pattern childGuard
    simpa only [d2301, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14436 pattern childGuard
    simpa only [d2301, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14438 (pattern : Twelve) (guard : d2301 pattern = 1) : d1343 pattern ≤ (2 : Int) + d2339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1343, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14321 pattern childGuard
    simpa only [d1343, d2339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1343, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14437 pattern childGuard
    simpa only [d1343, d2339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14439 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14440 (pattern : Twelve) (guard : d26 pattern = 1) : d1332 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14439 pattern childGuard
    simpa only [d26, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d26, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14441 (pattern : Twelve) (guard : d2301 pattern = 1) : d1338 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14440 pattern childGuard
    simpa only [d2301, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14275 pattern childGuard
    simpa only [d2301, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14442 (pattern : Twelve) (guard : d2301 pattern = 1) : d1344 pattern ≤ (2 : Int) + d2340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1344, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14441 pattern childGuard
    simpa only [d1344, d2340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1344, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1344, d2340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14443 (pattern : Twelve) (guard : d2301 pattern = 1) : d1348 pattern ≤ (2 : Int) + d2341 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1348, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14438 pattern childGuard
    simpa only [d1348, d2341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1348, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14442 pattern childGuard
    simpa only [d1348, d2341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14444 (pattern : Twelve) (guard : d2301 pattern = 1) : d1350 pattern ≤ (2 : Int) + d2342 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1350, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14432 pattern childGuard
    simpa only [d1350, d2342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1350, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14443 pattern childGuard
    simpa only [d1350, d2342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14445 (pattern : Twelve) (guard : d2301 pattern = 1) : d1351 pattern ≤ (2 : Int) + d2336 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1351, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14424 pattern childGuard
    simpa only [d1351, d2336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1351, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1351, d2336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14446 (pattern : Twelve) (guard : d2301 pattern = 1) : d1352 pattern ≤ (2 : Int) + d2343 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1352, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14444 pattern childGuard
    simpa only [d1352, d2343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1352, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14445 pattern childGuard
    simpa only [d1352, d2343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14447 (pattern : Twelve) (guard : d2301 pattern = 1) : d1353 pattern ≤ (2 : Int) + d2344 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1353, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14425 pattern childGuard
    simpa only [d1353, d2344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1353, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14446 pattern childGuard
    simpa only [d1353, d2344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14448 (pattern : Twelve) (guard : d2301 pattern = 1) : d1354 pattern ≤ (2 : Int) + d2345 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1354, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14412 pattern childGuard
    simpa only [d1354, d2345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1354, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14447 pattern childGuard
    simpa only [d1354, d2345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14449 (pattern : Twelve) (guard : d2301 pattern = 1) : d1656 pattern ≤ (2 : Int) + d1656 pattern := by
  omega
theorem c14450 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14451 (pattern : Twelve) (guard : d26 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14450 pattern childGuard
    simpa only [d26, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13455 pattern childGuard
    simpa only [d26, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14452 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14453 (pattern : Twelve) (guard : d2301 pattern = 1) : d1647 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14451 pattern childGuard
    simpa only [d2301, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14452 pattern childGuard
    simpa only [d2301, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14454 (pattern : Twelve) (guard : d2301 pattern = 1) : d1651 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14389 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14453 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14455 (pattern : Twelve) (guard : d2301 pattern = 1) : d1657 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14454 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14407 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14456 (pattern : Twelve) (guard : d2301 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14449 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14455 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14457 (pattern : Twelve) (guard : d0 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14458 (pattern : Twelve) (guard : d2301 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14451 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14457 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14459 (pattern : Twelve) (guard : d2301 pattern = 1) : d1652 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14397 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14458 pattern childGuard
    simpa only [d1652, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14460 (pattern : Twelve) (guard : d0 pattern = 1) : d821 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14461 (pattern : Twelve) (guard : d2301 pattern = 1) : d821 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14460 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14462 (pattern : Twelve) (guard : d2301 pattern = 1) : d1653 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14461 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1653, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14463 (pattern : Twelve) (guard : d2301 pattern = 1) : d1658 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14459 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14462 pattern childGuard
    simpa only [d1658, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14464 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (2 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14465 (pattern : Twelve) (guard : d26 pattern = 1) : d1646 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14464 pattern childGuard
    simpa only [d26, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d26, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14466 (pattern : Twelve) (guard : d2301 pattern = 1) : d1648 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14465 pattern childGuard
    simpa only [d2301, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14275 pattern childGuard
    simpa only [d2301, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14467 (pattern : Twelve) (guard : d2301 pattern = 1) : d1654 pattern ≤ (2 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1654, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14406 pattern childGuard
    simpa only [d1654, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1654, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14466 pattern childGuard
    simpa only [d1654, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14468 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (2 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14469 (pattern : Twelve) (guard : d26 pattern = 1) : d822 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14468 pattern childGuard
    simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13469 pattern childGuard
    simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14470 (pattern : Twelve) (guard : d2301 pattern = 1) : d822 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14469 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14325 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14471 (pattern : Twelve) (guard : d2301 pattern = 1) : d1655 pattern ≤ (2 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1655, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14470 pattern childGuard
    simpa only [d1655, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1655, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1655, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14472 (pattern : Twelve) (guard : d2301 pattern = 1) : d1659 pattern ≤ (2 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1659, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14467 pattern childGuard
    simpa only [d1659, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1659, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14471 pattern childGuard
    simpa only [d1659, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14473 (pattern : Twelve) (guard : d2301 pattern = 1) : d1661 pattern ≤ (2 : Int) + d1992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1661, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14463 pattern childGuard
    simpa only [d1661, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1661, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14472 pattern childGuard
    simpa only [d1661, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14474 (pattern : Twelve) (guard : d2301 pattern = 1) : d1662 pattern ≤ (2 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14455 pattern childGuard
    simpa only [d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1662, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14475 (pattern : Twelve) (guard : d2301 pattern = 1) : d1663 pattern ≤ (2 : Int) + d2346 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1663, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14473 pattern childGuard
    simpa only [d1663, d2346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1663, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14474 pattern childGuard
    simpa only [d1663, d2346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14476 (pattern : Twelve) (guard : d2301 pattern = 1) : d1664 pattern ≤ (2 : Int) + d2347 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1664, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14456 pattern childGuard
    simpa only [d1664, d2347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1664, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14475 pattern childGuard
    simpa only [d1664, d2347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14477 (pattern : Twelve) (guard : d2301 pattern = 1) : d19 pattern ≤ (2 : Int) + d19 pattern := by
  omega
theorem c14478 (pattern : Twelve) (guard : d2301 pattern = 1) : d1668 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14477 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14458 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14479 (pattern : Twelve) (guard : d2301 pattern = 1) : d1650 pattern ≤ (2 : Int) + d1650 pattern := by
  omega
theorem c14480 (pattern : Twelve) (guard : d2301 pattern = 1) : d1671 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14478 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14479 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14481 (pattern : Twelve) (guard : d2301 pattern = 1) : d1674 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14480 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14455 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14482 (pattern : Twelve) (guard : d0 pattern = 1) : d1665 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14483 (pattern : Twelve) (guard : d2301 pattern = 1) : d1666 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14451 pattern childGuard
    simpa only [d2301, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14482 pattern childGuard
    simpa only [d2301, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14484 (pattern : Twelve) (guard : d2301 pattern = 1) : d1669 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14397 pattern childGuard
    simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14483 pattern childGuard
    simpa only [d1669, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14485 (pattern : Twelve) (guard : d2301 pattern = 1) : d1672 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14484 pattern childGuard
    simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14407 pattern childGuard
    simpa only [d1672, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14486 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (2 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14487 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13468 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14488 (pattern : Twelve) (guard : d26 pattern = 1) : d128 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14486 pattern childGuard
    simpa only [d26, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14487 pattern childGuard
    simpa only [d26, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14489 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (2 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14490 (pattern : Twelve) (guard : d2301 pattern = 1) : d1667 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14488 pattern childGuard
    simpa only [d2301, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14489 pattern childGuard
    simpa only [d2301, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14491 (pattern : Twelve) (guard : d2301 pattern = 1) : d1670 pattern ≤ (2 : Int) + d2348 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1670, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14406 pattern childGuard
    simpa only [d1670, d2348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1670, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14490 pattern childGuard
    simpa only [d1670, d2348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14492 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14493 (pattern : Twelve) (guard : d26 pattern = 1) : d822 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14492 pattern childGuard
    simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d26, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14494 (pattern : Twelve) (guard : d2301 pattern = 1) : d1252 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14493 pattern childGuard
    simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14495 (pattern : Twelve) (guard : d2301 pattern = 1) : d1626 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14494 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14496 (pattern : Twelve) (guard : d2301 pattern = 1) : d1673 pattern ≤ (2 : Int) + d2349 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1673, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14491 pattern childGuard
    simpa only [d1673, d2349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1673, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14495 pattern childGuard
    simpa only [d1673, d2349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14497 (pattern : Twelve) (guard : d2301 pattern = 1) : d1675 pattern ≤ (2 : Int) + d2350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1675, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14485 pattern childGuard
    simpa only [d1675, d2350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1675, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14496 pattern childGuard
    simpa only [d1675, d2350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14498 (pattern : Twelve) (guard : d2301 pattern = 1) : d1676 pattern ≤ (2 : Int) + d2351 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1676, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14497 pattern childGuard
    simpa only [d1676, d2351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1676, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14474 pattern childGuard
    simpa only [d1676, d2351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14499 (pattern : Twelve) (guard : d2301 pattern = 1) : d1677 pattern ≤ (2 : Int) + d2352 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1677, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14481 pattern childGuard
    simpa only [d1677, d2352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1677, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14498 pattern childGuard
    simpa only [d1677, d2352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14500 (pattern : Twelve) (guard : d2301 pattern = 1) : d1678 pattern ≤ (2 : Int) + d2353 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1678, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14476 pattern childGuard
    simpa only [d1678, d2353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1678, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14499 pattern childGuard
    simpa only [d1678, d2353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14501 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  omega
theorem c14502 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14503 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14502 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14504 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14169 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14503 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14505 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14504 pattern childGuard
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14506 (pattern : Twelve) (guard : d0 pattern = 1) : d50 pattern ≤ (2 : Int) + d2357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14507 (pattern : Twelve) (guard : d2355 pattern = 1) : d72 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14505 pattern childGuard
    simpa only [d2355, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14506 pattern childGuard
    simpa only [d2355, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14508 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14509 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14510 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d3 pattern := by
  change (0 : Int) ≤ (2 : Int) + 3
  decide
theorem c14511 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14510 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14512 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14509 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14511 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14513 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14508 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14512 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14514 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14504 pattern childGuard
    simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14513 pattern childGuard
    simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14515 (pattern : Twelve) (guard : d0 pattern = 1) : d51 pattern ≤ (2 : Int) + d2358 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14516 (pattern : Twelve) (guard : d2355 pattern = 1) : d73 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14514 pattern childGuard
    simpa only [d2355, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14515 pattern childGuard
    simpa only [d2355, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14517 (pattern : Twelve) (guard : d2355 pattern = 1) : d91 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d91, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14507 pattern childGuard
    simpa only [d91, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d91, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14516 pattern childGuard
    simpa only [d91, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14518 (pattern : Twelve) (guard : d0 pattern = 1) : d208 pattern ≤ (2 : Int) + d2359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14519 (pattern : Twelve) (guard : d2356 pattern = 1) : d352 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14517 pattern childGuard
    simpa only [d2356, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14518 pattern childGuard
    simpa only [d2356, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14520 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (2 : Int) + d2358 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14521 (pattern : Twelve) (guard : d2355 pattern = 1) : d76 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14514 pattern childGuard
    simpa only [d2355, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14520 pattern childGuard
    simpa only [d2355, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14522 (pattern : Twelve) (guard : d2355 pattern = 1) : d93 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d93, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14507 pattern childGuard
    simpa only [d93, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d93, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14521 pattern childGuard
    simpa only [d93, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14523 (pattern : Twelve) (guard : d0 pattern = 1) : d209 pattern ≤ (2 : Int) + d2359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14524 (pattern : Twelve) (guard : d2356 pattern = 1) : d353 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14522 pattern childGuard
    simpa only [d2356, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14523 pattern childGuard
    simpa only [d2356, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14525 (pattern : Twelve) (guard : d2356 pattern = 1) : d358 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14519 pattern childGuard
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14524 pattern childGuard
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14526 (pattern : Twelve) (guard : d0 pattern = 1) : d211 pattern ≤ (2 : Int) + d2362 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14527 (pattern : Twelve) (guard : d2356 pattern = 1) : d354 pattern ≤ (2 : Int) + d2363 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d354, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14517 pattern childGuard
    simpa only [d2356, d354, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d354, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14526 pattern childGuard
    simpa only [d2356, d354, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14528 (pattern : Twelve) (guard : d2356 pattern = 1) : d355 pattern ≤ (2 : Int) + d2364 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d355, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14522 pattern childGuard
    simpa only [d2356, d355, d2364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d355, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d355, d2364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14529 (pattern : Twelve) (guard : d2356 pattern = 1) : d359 pattern ≤ (2 : Int) + d2365 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d359, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14527 pattern childGuard
    simpa only [d359, d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d359, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14528 pattern childGuard
    simpa only [d359, d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14530 (pattern : Twelve) (guard : d2356 pattern = 1) : d361 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d361, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14525 pattern childGuard
    simpa only [d361, d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d361, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14529 pattern childGuard
    simpa only [d361, d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14531 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14532 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13330 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14531 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14533 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14508 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14532 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14534 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14186 pattern childGuard
    simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14533 pattern childGuard
    simpa only [d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14535 (pattern : Twelve) (guard : d2355 pattern = 1) : d80 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14534 pattern childGuard
    simpa only [d2355, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14520 pattern childGuard
    simpa only [d2355, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14536 (pattern : Twelve) (guard : d2355 pattern = 1) : d97 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d97, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14507 pattern childGuard
    simpa only [d97, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d97, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14535 pattern childGuard
    simpa only [d97, d2359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14537 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14538 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14536 pattern childGuard
    simpa only [d2356, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14537 pattern childGuard
    simpa only [d2356, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14539 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2362 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14540 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2363 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d356, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14536 pattern childGuard
    simpa only [d2356, d356, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d356, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14539 pattern childGuard
    simpa only [d2356, d356, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14541 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2364 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d356, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14536 pattern childGuard
    simpa only [d2356, d356, d2364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d356, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d356, d2364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14542 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2365 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14540 pattern childGuard
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14541 pattern childGuard
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14543 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14538 pattern childGuard
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14542 pattern childGuard
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14544 (pattern : Twelve) (guard : d2356 pattern = 1) : d362 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14530 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14543 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14545 (pattern : Twelve) (guard : d2356 pattern = 1) : d357 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14517 pattern childGuard
    simpa only [d2356, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14537 pattern childGuard
    simpa only [d2356, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14546 (pattern : Twelve) (guard : d2356 pattern = 1) : d355 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14522 pattern childGuard
    simpa only [d2356, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14537 pattern childGuard
    simpa only [d2356, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14547 (pattern : Twelve) (guard : d2356 pattern = 1) : d360 pattern ≤ (2 : Int) + d2359 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14545 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14546 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14548 (pattern : Twelve) (guard : d2356 pattern = 1) : d357 pattern ≤ (2 : Int) + d2363 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d357, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14517 pattern childGuard
    simpa only [d2356, d357, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d357, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14539 pattern childGuard
    simpa only [d2356, d357, d2363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14549 (pattern : Twelve) (guard : d2356 pattern = 1) : d360 pattern ≤ (2 : Int) + d2365 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14548 pattern childGuard
    simpa only [d360, d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14528 pattern childGuard
    simpa only [d360, d2365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14550 (pattern : Twelve) (guard : d2356 pattern = 1) : d360 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14547 pattern childGuard
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14549 pattern childGuard
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14551 (pattern : Twelve) (guard : d2356 pattern = 1) : d363 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14550 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14543 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14552 (pattern : Twelve) (guard : d2356 pattern = 1) : d364 pattern ≤ (2 : Int) + d2366 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14544 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14551 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14553 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2369 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14554 (pattern : Twelve) (guard : d2356 pattern = 1) : d357 pattern ≤ (2 : Int) + d2370 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d357, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14517 pattern childGuard
    simpa only [d2356, d357, d2370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d357, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14553 pattern childGuard
    simpa only [d2356, d357, d2370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14555 (pattern : Twelve) (guard : d2356 pattern = 1) : d360 pattern ≤ (2 : Int) + d2371 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14554 pattern childGuard
    simpa only [d360, d2371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d360, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14528 pattern childGuard
    simpa only [d360, d2371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14556 (pattern : Twelve) (guard : d2356 pattern = 1) : d360 pattern ≤ (2 : Int) + d2372 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14547 pattern childGuard
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14555 pattern childGuard
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14557 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2370 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d356, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14536 pattern childGuard
    simpa only [d2356, d356, d2370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d356, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14553 pattern childGuard
    simpa only [d2356, d356, d2370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14558 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2371 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14557 pattern childGuard
    simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14541 pattern childGuard
    simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14559 (pattern : Twelve) (guard : d2356 pattern = 1) : d356 pattern ≤ (2 : Int) + d2372 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14538 pattern childGuard
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14558 pattern childGuard
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
