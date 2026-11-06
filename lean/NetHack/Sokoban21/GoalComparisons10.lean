/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons09
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC1300 (pattern : Twelve) (guard : d3255 pattern = 1) : d1450 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC958 pattern childGuard
    simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1299 pattern childGuard
    simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1301 (pattern : Twelve) (guard : d0 pattern = 1) : d1449 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1302 (pattern : Twelve) (guard : d3259 pattern = 1) : d1456 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1300 pattern childGuard
    simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1301 pattern childGuard
    simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1303 (pattern : Twelve) (guard : d0 pattern = 1) : d1457 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1304 (pattern : Twelve) (guard : d3263 pattern = 1) : d1460 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1460, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1302 pattern childGuard
    simpa only [d3263, d1460, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1460, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1303 pattern childGuard
    simpa only [d3263, d1460, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1305 (pattern : Twelve) (guard : d0 pattern = 1) : d1461 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1306 (pattern : Twelve) (guard : d3267 pattern = 1) : d1464 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1464, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1304 pattern childGuard
    simpa only [d3267, d1464, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1464, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1305 pattern childGuard
    simpa only [d3267, d1464, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1307 (pattern : Twelve) (guard : d3268 pattern = 1) : d1466 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1466, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1298 pattern childGuard
    simpa only [d3268, d1466, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1466, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1306 pattern childGuard
    simpa only [d3268, d1466, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1308 (pattern : Twelve) (guard : d3271 pattern = 1) : d1467 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1467 pattern).2
  change d1467 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1309 (pattern : Twelve) (guard : d3272 pattern = 1) : d1469 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1469, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1307 pattern childGuard
    simpa only [d3272, d1469, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1469, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1308 pattern childGuard
    simpa only [d3272, d1469, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1310 (pattern : Twelve) (guard : d3275 pattern = 1) : d1467 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1467 pattern).2
  change d1467 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1311 (pattern : Twelve) (guard : d3276 pattern = 1) : d1470 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1470, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1309 pattern childGuard
    simpa only [d3276, d1470, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1470, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1310 pattern childGuard
    simpa only [d3276, d1470, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1312 (pattern : Twelve) (guard : d3278 pattern = 1) : d1468 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1468 pattern).2
  change d1468 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1313 (pattern : Twelve) (guard : d3279 pattern = 1) : d1471 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1471, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1311 pattern childGuard
    simpa only [d3279, d1471, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1471, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1312 pattern childGuard
    simpa only [d3279, d1471, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1314 (pattern : Twelve) (guard : d3256 pattern = 1) : d1472 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC980 pattern childGuard
    simpa only [d3256, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1147 pattern childGuard
    simpa only [d3256, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1315 (pattern : Twelve) (guard : d3259 pattern = 1) : d1473 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC983 pattern childGuard
    simpa only [d3259, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1151 pattern childGuard
    simpa only [d3259, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1316 (pattern : Twelve) (guard : d3260 pattern = 1) : d1479 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1479, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1314 pattern childGuard
    simpa only [d3260, d1479, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1479, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1315 pattern childGuard
    simpa only [d3260, d1479, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1317 (pattern : Twelve) (guard : d3259 pattern = 1) : d1474 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC986 pattern childGuard
    simpa only [d3259, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1156 pattern childGuard
    simpa only [d3259, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1318 (pattern : Twelve) (guard : d0 pattern = 1) : d1473 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1319 (pattern : Twelve) (guard : d3263 pattern = 1) : d1480 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1480, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1317 pattern childGuard
    simpa only [d3263, d1480, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1480, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1318 pattern childGuard
    simpa only [d3263, d1480, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1320 (pattern : Twelve) (guard : d3264 pattern = 1) : d1484 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1484, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1316 pattern childGuard
    simpa only [d3264, d1484, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1484, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1319 pattern childGuard
    simpa only [d3264, d1484, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1321 (pattern : Twelve) (guard : d3259 pattern = 1) : d1475 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC992 pattern childGuard
    simpa only [d3259, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1163 pattern childGuard
    simpa only [d3259, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1322 (pattern : Twelve) (guard : d0 pattern = 1) : d1476 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1323 (pattern : Twelve) (guard : d3263 pattern = 1) : d1481 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1481, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1321 pattern childGuard
    simpa only [d3263, d1481, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1481, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1322 pattern childGuard
    simpa only [d3263, d1481, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1324 (pattern : Twelve) (guard : d0 pattern = 1) : d1482 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1325 (pattern : Twelve) (guard : d3267 pattern = 1) : d1485 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1485, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1323 pattern childGuard
    simpa only [d3267, d1485, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1485, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1324 pattern childGuard
    simpa only [d3267, d1485, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1326 (pattern : Twelve) (guard : d3268 pattern = 1) : d1487 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1487, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1320 pattern childGuard
    simpa only [d3268, d1487, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1487, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1325 pattern childGuard
    simpa only [d3268, d1487, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1327 (pattern : Twelve) (guard : d3271 pattern = 1) : d1488 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1488 pattern).2
  change d1488 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1328 (pattern : Twelve) (guard : d3272 pattern = 1) : d1490 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1490, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1326 pattern childGuard
    simpa only [d3272, d1490, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1490, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1327 pattern childGuard
    simpa only [d3272, d1490, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1329 (pattern : Twelve) (guard : d3275 pattern = 1) : d1488 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1488 pattern).2
  change d1488 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1330 (pattern : Twelve) (guard : d3276 pattern = 1) : d1491 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1491, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1328 pattern childGuard
    simpa only [d3276, d1491, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1491, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1329 pattern childGuard
    simpa only [d3276, d1491, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1331 (pattern : Twelve) (guard : d3278 pattern = 1) : d1489 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1489 pattern).2
  change d1489 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1332 (pattern : Twelve) (guard : d3279 pattern = 1) : d1492 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1492, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1330 pattern childGuard
    simpa only [d3279, d1492, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1492, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1331 pattern childGuard
    simpa only [d3279, d1492, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1333 (pattern : Twelve) (guard : d0 pattern = 1) : d479 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1334 (pattern : Twelve) (guard : d3251 pattern = 1) : d1505 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1010 pattern childGuard
    simpa only [d3251, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1333 pattern childGuard
    simpa only [d3251, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1335 (pattern : Twelve) (guard : d3252 pattern = 1) : d1517 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1016 pattern childGuard
    simpa only [d3252, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1334 pattern childGuard
    simpa only [d3252, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1336 (pattern : Twelve) (guard : d0 pattern = 1) : d482 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1337 (pattern : Twelve) (guard : d3247 pattern = 1) : d482 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC468 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1336 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1338 (pattern : Twelve) (guard : d0 pattern = 1) : d482 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1339 (pattern : Twelve) (guard : d3251 pattern = 1) : d482 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1337 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1338 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1340 (pattern : Twelve) (guard : d3255 pattern = 1) : d1518 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1339 pattern childGuard
    simpa only [d3255, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1341 (pattern : Twelve) (guard : d3256 pattern = 1) : d1532 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1335 pattern childGuard
    simpa only [d3256, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1340 pattern childGuard
    simpa only [d3256, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1342 (pattern : Twelve) (guard : d0 pattern = 1) : d1506 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1343 (pattern : Twelve) (guard : d3255 pattern = 1) : d1519 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1029 pattern childGuard
    simpa only [d3255, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1342 pattern childGuard
    simpa only [d3255, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1344 (pattern : Twelve) (guard : d0 pattern = 1) : d1520 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1345 (pattern : Twelve) (guard : d3259 pattern = 1) : d1533 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1343 pattern childGuard
    simpa only [d3259, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1344 pattern childGuard
    simpa only [d3259, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1346 (pattern : Twelve) (guard : d3260 pattern = 1) : d1541 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1541, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1341 pattern childGuard
    simpa only [d3260, d1541, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1541, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1345 pattern childGuard
    simpa only [d3260, d1541, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1347 (pattern : Twelve) (guard : d0 pattern = 1) : d1505 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1348 (pattern : Twelve) (guard : d3255 pattern = 1) : d1521 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1038 pattern childGuard
    simpa only [d3255, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1347 pattern childGuard
    simpa only [d3255, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1349 (pattern : Twelve) (guard : d0 pattern = 1) : d1518 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1350 (pattern : Twelve) (guard : d3259 pattern = 1) : d1534 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1348 pattern childGuard
    simpa only [d3259, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1349 pattern childGuard
    simpa only [d3259, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1351 (pattern : Twelve) (guard : d0 pattern = 1) : d1533 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1352 (pattern : Twelve) (guard : d3263 pattern = 1) : d1542 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1542, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1350 pattern childGuard
    simpa only [d3263, d1542, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1542, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1351 pattern childGuard
    simpa only [d3263, d1542, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1353 (pattern : Twelve) (guard : d3264 pattern = 1) : d1548 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1548, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1346 pattern childGuard
    simpa only [d3264, d1548, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1548, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1352 pattern childGuard
    simpa only [d3264, d1548, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1354 (pattern : Twelve) (guard : d0 pattern = 1) : d1508 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1355 (pattern : Twelve) (guard : d3255 pattern = 1) : d1522 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1051 pattern childGuard
    simpa only [d3255, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1354 pattern childGuard
    simpa only [d3255, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1356 (pattern : Twelve) (guard : d0 pattern = 1) : d1523 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1357 (pattern : Twelve) (guard : d3259 pattern = 1) : d1535 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1355 pattern childGuard
    simpa only [d3259, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1356 pattern childGuard
    simpa only [d3259, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1358 (pattern : Twelve) (guard : d0 pattern = 1) : d1536 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1359 (pattern : Twelve) (guard : d3263 pattern = 1) : d1543 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1543, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1357 pattern childGuard
    simpa only [d3263, d1543, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1543, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1358 pattern childGuard
    simpa only [d3263, d1543, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1360 (pattern : Twelve) (guard : d0 pattern = 1) : d1544 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1361 (pattern : Twelve) (guard : d3267 pattern = 1) : d1549 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1549, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1359 pattern childGuard
    simpa only [d3267, d1549, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1549, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1360 pattern childGuard
    simpa only [d3267, d1549, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1362 (pattern : Twelve) (guard : d3268 pattern = 1) : d1551 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1551, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1353 pattern childGuard
    simpa only [d3268, d1551, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1551, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1361 pattern childGuard
    simpa only [d3268, d1551, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1363 (pattern : Twelve) (guard : d3271 pattern = 1) : d1552 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1552 pattern).2
  change d1552 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1364 (pattern : Twelve) (guard : d3272 pattern = 1) : d1554 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1554, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1362 pattern childGuard
    simpa only [d3272, d1554, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1554, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1363 pattern childGuard
    simpa only [d3272, d1554, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1365 (pattern : Twelve) (guard : d3275 pattern = 1) : d1552 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1552 pattern).2
  change d1552 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1366 (pattern : Twelve) (guard : d3276 pattern = 1) : d1555 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1555, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1364 pattern childGuard
    simpa only [d3276, d1555, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1555, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1365 pattern childGuard
    simpa only [d3276, d1555, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1367 (pattern : Twelve) (guard : d3278 pattern = 1) : d1553 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1553 pattern).2
  change d1553 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1368 (pattern : Twelve) (guard : d3279 pattern = 1) : d1556 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1556, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1366 pattern childGuard
    simpa only [d3279, d1556, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1556, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1367 pattern childGuard
    simpa only [d3279, d1556, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1369 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1370 (pattern : Twelve) (guard : d3251 pattern = 1) : d1564 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1073 pattern childGuard
    simpa only [d3251, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1369 pattern childGuard
    simpa only [d3251, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1371 (pattern : Twelve) (guard : d3252 pattern = 1) : d1576 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1077 pattern childGuard
    simpa only [d3252, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1370 pattern childGuard
    simpa only [d3252, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1372 (pattern : Twelve) (guard : d0 pattern = 1) : d636 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1373 (pattern : Twelve) (guard : d3247 pattern = 1) : d636 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC603 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1372 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1374 (pattern : Twelve) (guard : d0 pattern = 1) : d636 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1375 (pattern : Twelve) (guard : d3251 pattern = 1) : d636 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1373 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1374 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1376 (pattern : Twelve) (guard : d3255 pattern = 1) : d1577 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1375 pattern childGuard
    simpa only [d3255, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1377 (pattern : Twelve) (guard : d3256 pattern = 1) : d1591 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1371 pattern childGuard
    simpa only [d3256, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1376 pattern childGuard
    simpa only [d3256, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1378 (pattern : Twelve) (guard : d0 pattern = 1) : d1565 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1379 (pattern : Twelve) (guard : d3255 pattern = 1) : d1578 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1088 pattern childGuard
    simpa only [d3255, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1378 pattern childGuard
    simpa only [d3255, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1380 (pattern : Twelve) (guard : d0 pattern = 1) : d1579 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1381 (pattern : Twelve) (guard : d3259 pattern = 1) : d1592 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1379 pattern childGuard
    simpa only [d3259, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1380 pattern childGuard
    simpa only [d3259, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1382 (pattern : Twelve) (guard : d3260 pattern = 1) : d1600 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1600, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1377 pattern childGuard
    simpa only [d3260, d1600, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1600, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1381 pattern childGuard
    simpa only [d3260, d1600, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1383 (pattern : Twelve) (guard : d0 pattern = 1) : d1564 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1384 (pattern : Twelve) (guard : d3255 pattern = 1) : d1580 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1097 pattern childGuard
    simpa only [d3255, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1383 pattern childGuard
    simpa only [d3255, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1385 (pattern : Twelve) (guard : d0 pattern = 1) : d1577 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1386 (pattern : Twelve) (guard : d3259 pattern = 1) : d1593 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1384 pattern childGuard
    simpa only [d3259, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1385 pattern childGuard
    simpa only [d3259, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1387 (pattern : Twelve) (guard : d0 pattern = 1) : d1592 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1388 (pattern : Twelve) (guard : d3263 pattern = 1) : d1601 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1601, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1386 pattern childGuard
    simpa only [d3263, d1601, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1601, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1387 pattern childGuard
    simpa only [d3263, d1601, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1389 (pattern : Twelve) (guard : d3264 pattern = 1) : d1607 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1607, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1382 pattern childGuard
    simpa only [d3264, d1607, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1607, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1388 pattern childGuard
    simpa only [d3264, d1607, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1390 (pattern : Twelve) (guard : d0 pattern = 1) : d1567 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1391 (pattern : Twelve) (guard : d3255 pattern = 1) : d1581 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1108 pattern childGuard
    simpa only [d3255, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1390 pattern childGuard
    simpa only [d3255, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1392 (pattern : Twelve) (guard : d0 pattern = 1) : d1582 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1393 (pattern : Twelve) (guard : d3259 pattern = 1) : d1594 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1391 pattern childGuard
    simpa only [d3259, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1392 pattern childGuard
    simpa only [d3259, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1394 (pattern : Twelve) (guard : d0 pattern = 1) : d1595 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1395 (pattern : Twelve) (guard : d3263 pattern = 1) : d1602 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1602, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1393 pattern childGuard
    simpa only [d3263, d1602, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1602, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1394 pattern childGuard
    simpa only [d3263, d1602, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1396 (pattern : Twelve) (guard : d0 pattern = 1) : d1603 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1397 (pattern : Twelve) (guard : d3267 pattern = 1) : d1608 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1608, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1395 pattern childGuard
    simpa only [d3267, d1608, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1608, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1396 pattern childGuard
    simpa only [d3267, d1608, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1398 (pattern : Twelve) (guard : d3268 pattern = 1) : d1610 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1610, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1389 pattern childGuard
    simpa only [d3268, d1610, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1610, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1397 pattern childGuard
    simpa only [d3268, d1610, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1399 (pattern : Twelve) (guard : d3271 pattern = 1) : d1611 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1611 pattern).2
  change d1611 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1400 (pattern : Twelve) (guard : d3272 pattern = 1) : d1613 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1613, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1398 pattern childGuard
    simpa only [d3272, d1613, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1613, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1399 pattern childGuard
    simpa only [d3272, d1613, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1401 (pattern : Twelve) (guard : d3275 pattern = 1) : d1611 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1611 pattern).2
  change d1611 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1402 (pattern : Twelve) (guard : d3276 pattern = 1) : d1614 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1614, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1400 pattern childGuard
    simpa only [d3276, d1614, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1614, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1401 pattern childGuard
    simpa only [d3276, d1614, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1403 (pattern : Twelve) (guard : d3278 pattern = 1) : d1612 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1612 pattern).2
  change d1612 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1404 (pattern : Twelve) (guard : d3279 pattern = 1) : d1615 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1615, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1402 pattern childGuard
    simpa only [d3279, d1615, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1615, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1403 pattern childGuard
    simpa only [d3279, d1615, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1405 (pattern : Twelve) (guard : d3278 pattern = 1) : d1635 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1635 pattern).2
  change d1635 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1406 (pattern : Twelve) (guard : d3279 pattern = 1) : d1636 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1636, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1173 pattern childGuard
    simpa only [d3279, d1636, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1636, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1405 pattern childGuard
    simpa only [d3279, d1636, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1407 (pattern : Twelve) (guard : d3272 pattern = 1) : d1637 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1637, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1169 pattern childGuard
    simpa only [d3272, d1637, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1637, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1193 pattern childGuard
    simpa only [d3272, d1637, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1408 (pattern : Twelve) (guard : d3275 pattern = 1) : d1637 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1637 pattern).2
  change d1637 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1409 (pattern : Twelve) (guard : d3276 pattern = 1) : d1637 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1407 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1408 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1410 (pattern : Twelve) (guard : d3278 pattern = 1) : d1638 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1638 pattern).2
  change d1638 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1411 (pattern : Twelve) (guard : d3279 pattern = 1) : d1639 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1639, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1409 pattern childGuard
    simpa only [d3279, d1639, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1639, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1410 pattern childGuard
    simpa only [d3279, d1639, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1412 (pattern : Twelve) (guard : d3276 pattern = 1) : d1640 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1640, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1171 pattern childGuard
    simpa only [d3276, d1640, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1640, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1195 pattern childGuard
    simpa only [d3276, d1640, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1413 (pattern : Twelve) (guard : d3278 pattern = 1) : d1641 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1641 pattern).2
  change d1641 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1414 (pattern : Twelve) (guard : d3279 pattern = 1) : d1642 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1642, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1412 pattern childGuard
    simpa only [d3279, d1642, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1642, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1413 pattern childGuard
    simpa only [d3279, d1642, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1415 (pattern : Twelve) (guard : d3279 pattern = 1) : d1643 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1643, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1173 pattern childGuard
    simpa only [d3279, d1643, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1643, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1197 pattern childGuard
    simpa only [d3279, d1643, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1416 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1417 (pattern : Twelve) (guard : d3255 pattern = 1) : d1649 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1146 pattern childGuard
    simpa only [d3255, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1416 pattern childGuard
    simpa only [d3255, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1418 (pattern : Twelve) (guard : d0 pattern = 1) : d1650 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1419 (pattern : Twelve) (guard : d3259 pattern = 1) : d1656 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1417 pattern childGuard
    simpa only [d3259, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1418 pattern childGuard
    simpa only [d3259, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1420 (pattern : Twelve) (guard : d0 pattern = 1) : d1657 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1421 (pattern : Twelve) (guard : d3263 pattern = 1) : d1660 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1660, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1419 pattern childGuard
    simpa only [d3263, d1660, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1660, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1420 pattern childGuard
    simpa only [d3263, d1660, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1422 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (0 : Int) + d3283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1423 (pattern : Twelve) (guard : d3267 pattern = 1) : d1660 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1421 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1422 pattern childGuard
    simpa only [d3267, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1424 (pattern : Twelve) (guard : d0 pattern = 1) : d1663 pattern ≤ (0 : Int) + d3288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1425 (pattern : Twelve) (guard : d3271 pattern = 1) : d1664 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3271, d1664, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1423 pattern childGuard
    simpa only [d3271, d1664, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3271, d1664, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1424 pattern childGuard
    simpa only [d3271, d1664, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1426 (pattern : Twelve) (guard : d3275 pattern = 1) : d1664 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1425 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d3275, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1427 (pattern : Twelve) (guard : d3278 pattern = 1) : d1664 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1426 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d3278, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1428 (pattern : Twelve) (guard : d3280 pattern = 1) : d1664 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1427 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9579 pattern childGuard
    simpa only [d3280, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1429 (pattern : Twelve) (guard : d3280 pattern = 1) : d1678 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3280, d1678, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1427 pattern childGuard
    simpa only [d3280, d1678, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3280, d1678, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9582 pattern childGuard
    simpa only [d3280, d1678, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
