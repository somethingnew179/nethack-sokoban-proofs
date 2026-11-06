/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons152
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21420 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (2 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21417 pattern childGuard
    simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21419 pattern childGuard
    simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21421 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (2 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20570 pattern childGuard
    simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21347 pattern childGuard
    simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21422 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (2 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20395 pattern childGuard
    simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21421 pattern childGuard
    simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21423 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (2 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20570 pattern childGuard
    simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21350 pattern childGuard
    simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21424 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (2 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20601 pattern childGuard
    simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20614 pattern childGuard
    simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21425 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (2 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21423 pattern childGuard
    simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21424 pattern childGuard
    simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21426 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (2 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21422 pattern childGuard
    simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21425 pattern childGuard
    simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21427 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (2 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21420 pattern childGuard
    simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21426 pattern childGuard
    simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21428 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (2 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21414 pattern childGuard
    simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21429 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (2 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21427 pattern childGuard
    simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21428 pattern childGuard
    simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21430 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (2 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21415 pattern childGuard
    simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21429 pattern childGuard
    simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21431 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (2 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21402 pattern childGuard
    simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21430 pattern childGuard
    simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21432 (pattern : Twelve) (guard : d0 pattern = 1) : d1266 pattern ≤ (2 : Int) + d1266 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21433 (pattern : Twelve) (guard : d1878 pattern = 1) : d1267 pattern ≤ (2 : Int) + d1266 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21431 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21432 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21434 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13320 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21435 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21434 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21262 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21436 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (2 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13409 pattern childGuard
    simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21435 pattern childGuard
    simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21437 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21435 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21438 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (2 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21436 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21437 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21439 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (2 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21438 pattern childGuard
    simpa only [d1293, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21440 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (2 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21439 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21159 pattern childGuard
    simpa only [d1305, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21441 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20328 pattern childGuard
    simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21161 pattern childGuard
    simpa only [d1276, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21442 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (2 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13409 pattern childGuard
    simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21441 pattern childGuard
    simpa only [d1279, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21443 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (2 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21442 pattern childGuard
    simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21164 pattern childGuard
    simpa only [d1285, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21444 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (2 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21101 pattern childGuard
    simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21443 pattern childGuard
    simpa only [d1295, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21445 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (2 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21444 pattern childGuard
    simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21167 pattern childGuard
    simpa only [d1306, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21446 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21440 pattern childGuard
    simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21445 pattern childGuard
    simpa only [d1313, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21447 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (2 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20551 pattern childGuard
    simpa only [d1281, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21448 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (2 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21442 pattern childGuard
    simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21447 pattern childGuard
    simpa only [d1287, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21449 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21448 pattern childGuard
    simpa only [d1297, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21450 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21312 pattern childGuard
    simpa only [d817, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21451 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21450 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21452 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (2 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21451 pattern childGuard
    simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1298, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21453 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (2 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21449 pattern childGuard
    simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21452 pattern childGuard
    simpa only [d1307, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21454 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13591 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13613 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21455 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (2 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21178 pattern childGuard
    simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21454 pattern childGuard
    simpa only [d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21456 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20551 pattern childGuard
    simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21457 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (2 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21455 pattern childGuard
    simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21456 pattern childGuard
    simpa only [d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21458 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (2 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21177 pattern childGuard
    simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21457 pattern childGuard
    simpa only [d1299, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21459 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21460 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21459 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13613 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21461 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (2 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21460 pattern childGuard
    simpa only [d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21462 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21461 pattern childGuard
    simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21313 pattern childGuard
    simpa only [d1289, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21463 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21462 pattern childGuard
    simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1300, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21464 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (2 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21458 pattern childGuard
    simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21463 pattern childGuard
    simpa only [d1308, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21465 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (2 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21453 pattern childGuard
    simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21464 pattern childGuard
    simpa only [d1314, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21466 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (2 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21445 pattern childGuard
    simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21467 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (2 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21465 pattern childGuard
    simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21466 pattern childGuard
    simpa only [d1319, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21468 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (2 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21446 pattern childGuard
    simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21467 pattern childGuard
    simpa only [d1321, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21469 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (2 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20536 pattern childGuard
    simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1278, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21470 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (2 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21469 pattern childGuard
    simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1284, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21471 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (2 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21470 pattern childGuard
    simpa only [d1293, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21472 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (2 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d1283, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21473 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (2 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21472 pattern childGuard
    simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1301, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21474 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (2 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21471 pattern childGuard
    simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21473 pattern childGuard
    simpa only [d1309, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21475 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (2 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20536 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20573 pattern childGuard
    simpa only [d1279, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21476 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (2 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21475 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20553 pattern childGuard
    simpa only [d1285, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21477 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (2 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20549 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21476 pattern childGuard
    simpa only [d1295, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21478 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20571 pattern childGuard
    simpa only [d1290, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21479 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21478 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1302, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21480 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (2 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21477 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21479 pattern childGuard
    simpa only [d1310, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21481 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (2 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21474 pattern childGuard
    simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21480 pattern childGuard
    simpa only [d1316, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21482 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20550 pattern childGuard
    simpa only [d119, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21483 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (2 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21482 pattern childGuard
    simpa only [d1281, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21484 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (2 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21475 pattern childGuard
    simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21483 pattern childGuard
    simpa only [d1287, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21485 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21484 pattern childGuard
    simpa only [d1297, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21486 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20570 pattern childGuard
    simpa only [d1291, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21487 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21486 pattern childGuard
    simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1303, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21488 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (2 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21485 pattern childGuard
    simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21487 pattern childGuard
    simpa only [d1311, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21489 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (2 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20573 pattern childGuard
    simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21454 pattern childGuard
    simpa only [d1282, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21490 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21482 pattern childGuard
    simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21491 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (2 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21489 pattern childGuard
    simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21490 pattern childGuard
    simpa only [d1288, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21492 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (2 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20572 pattern childGuard
    simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21491 pattern childGuard
    simpa only [d1299, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21493 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (2 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20601 pattern childGuard
    simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21352 pattern childGuard
    simpa only [d1292, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21494 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (2 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21493 pattern childGuard
    simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1304, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21495 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (2 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21492 pattern childGuard
    simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21494 pattern childGuard
    simpa only [d1312, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21496 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (2 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21488 pattern childGuard
    simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21495 pattern childGuard
    simpa only [d1317, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21497 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (2 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21480 pattern childGuard
    simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1318, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21498 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (2 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21496 pattern childGuard
    simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21497 pattern childGuard
    simpa only [d1320, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21499 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (2 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21481 pattern childGuard
    simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21498 pattern childGuard
    simpa only [d1322, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21500 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (2 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21468 pattern childGuard
    simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21499 pattern childGuard
    simpa only [d1323, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21501 (pattern : Twelve) (guard : d0 pattern = 1) : d1635 pattern ≤ (2 : Int) + d1635 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21502 (pattern : Twelve) (guard : d1878 pattern = 1) : d1636 pattern ≤ (2 : Int) + d1635 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21500 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21501 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21503 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (2 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21504 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (2 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21503 pattern childGuard
    simpa only [d1649, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21505 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (2 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21504 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21222 pattern childGuard
    simpa only [d1656, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21506 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21505 pattern childGuard
    simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13621 pattern childGuard
    simpa only [d1660, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21507 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20360 pattern childGuard
    simpa only [d1644, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21508 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13606 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21507 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21509 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (2 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21508 pattern childGuard
    simpa only [d1652, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21510 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (2 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21509 pattern childGuard
    simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13617 pattern childGuard
    simpa only [d1658, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21511 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (2 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20591 pattern childGuard
    simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21512 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (2 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21511 pattern childGuard
    simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20610 pattern childGuard
    simpa only [d1648, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21513 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (2 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21231 pattern childGuard
    simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21512 pattern childGuard
    simpa only [d1654, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21514 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21236 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20614 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21515 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (2 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21514 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21516 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (2 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21513 pattern childGuard
    simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21515 pattern childGuard
    simpa only [d1659, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21517 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (2 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21510 pattern childGuard
    simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21516 pattern childGuard
    simpa only [d1661, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21518 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (2 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21517 pattern childGuard
    simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21241 pattern childGuard
    simpa only [d1663, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21519 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21506 pattern childGuard
    simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21518 pattern childGuard
    simpa only [d1664, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21520 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (2 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20590 pattern childGuard
    simpa only [d1649, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21521 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (2 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21520 pattern childGuard
    simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20594 pattern childGuard
    simpa only [d1656, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21522 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21521 pattern childGuard
    simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20604 pattern childGuard
    simpa only [d1660, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21523 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (2 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20597 pattern childGuard
    simpa only [d1652, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21524 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (2 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20601 pattern childGuard
    simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1653, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21525 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (2 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21523 pattern childGuard
    simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21524 pattern childGuard
    simpa only [d1658, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21526 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20360 pattern childGuard
    simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d1646, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21527 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21526 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20610 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21528 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (2 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20602 pattern childGuard
    simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21527 pattern childGuard
    simpa only [d1654, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21529 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20614 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21530 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (2 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21528 pattern childGuard
    simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21529 pattern childGuard
    simpa only [d1659, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21531 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (2 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21525 pattern childGuard
    simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21530 pattern childGuard
    simpa only [d1661, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21532 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (2 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21531 pattern childGuard
    simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20619 pattern childGuard
    simpa only [d1663, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21533 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21522 pattern childGuard
    simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21532 pattern childGuard
    simpa only [d1664, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21534 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21519 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21533 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21535 (pattern : Twelve) (guard : d0 pattern = 1) : d1826 pattern ≤ (2 : Int) + d1826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21536 (pattern : Twelve) (guard : d1878 pattern = 1) : d1827 pattern ≤ (2 : Int) + d1826 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21534 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21535 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21537 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d0 pattern := by
  omega
theorem c21538 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d1 pattern := by
  change (0 : Int) ≤ (18 : Int) + 1
  decide
theorem c21539 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21537 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21538 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21540 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21537 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21539 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21541 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (18 : Int) + d1 pattern := by
  omega
theorem c21542 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (18 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21540 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21541 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21543 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (18 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21538 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21541 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21544 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (18 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21539 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21543 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21545 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (18 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21544 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21541 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21546 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (18 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21542 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21545 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21547 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (18 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21537 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21546 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21548 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d2 pattern := by
  change (0 : Int) ≤ (18 : Int) + 2
  decide
theorem c21549 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (18 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21537 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21548 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21550 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (18 : Int) + d3 pattern := by
  change (1 : Int) ≤ (18 : Int) + 3
  decide
theorem c21551 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (18 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21538 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21550 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21552 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (18 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21549 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21551 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21553 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (18 : Int) + d2 pattern := by
  change (1 : Int) ≤ (18 : Int) + 2
  decide
theorem c21554 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (18 : Int) + d4 pattern := by
  change (2 : Int) ≤ (18 : Int) + 4
  decide
theorem c21555 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (18 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21553 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21554 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21556 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (18 : Int) + d3 pattern := by
  change (2 : Int) ≤ (18 : Int) + 3
  decide
theorem c21557 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (18 : Int) + d5 pattern := by
  change (3 : Int) ≤ (18 : Int) + 5
  decide
theorem c21558 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (18 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21556 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21557 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21559 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (18 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21555 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21558 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
