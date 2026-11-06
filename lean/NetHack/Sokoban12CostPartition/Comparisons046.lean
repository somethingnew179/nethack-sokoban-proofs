/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6440 (p : Pattern) (guard : d1332 p = 1) : d188 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d1332, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6441 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6442 (p : Pattern) (guard : d1335 p = 1) : d250 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d1335, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6441 p hg
    simpa only [d1335, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6443 (p : Pattern) (guard : d1338 p = 1) : d251 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d1338, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6444 (p : Pattern) (guard : d1339 p = 1) : d252 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6436 p hg
    simpa only [d1339, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d1339, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6445 (p : Pattern) (guard : d1332 p = 1) : d191 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d1332, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6446 (p : Pattern) (guard : d0 p = 1) : d253 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6447 (p : Pattern) (guard : d1335 p = 1) : d254 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1335, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6446 p hg
    simpa only [d1335, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6448 (p : Pattern) (guard : d1338 p = 1) : d255 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d1338, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6449 (p : Pattern) (guard : d1341 p = 1) : d256 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6448 p hg
    simpa only [d1341, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6450 (p : Pattern) (guard : d1342 p = 1) : d257 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d1342, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d1342, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6451 (p : Pattern) (guard : d1343 p = 1) : d258 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d258, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6429 p hg
    simpa only [d1343, d258, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d258, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6450 p hg
    simpa only [d1343, d258, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6452 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6453 (p : Pattern) (guard : d1314 p = 1) : d7 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6318 p hg
    simpa only [d1314, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d1314, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6454 (p : Pattern) (guard : d1317 p = 1) : d7 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6455 (p : Pattern) (guard : d1320 p = 1) : d7 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6456 (p : Pattern) (guard : d1321 p = 1) : d7 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6455 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6457 (p : Pattern) (guard : d1324 p = 1) : d57 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6456 p hg
    simpa only [d1324, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1324, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6458 (p : Pattern) (guard : d1327 p = 1) : d57 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6457 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6459 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6460 (p : Pattern) (guard : d1329 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6459 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6461 (p : Pattern) (guard : d1330 p = 1) : d57 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6458 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6462 (p : Pattern) (guard : d1331 p = 1) : d57 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6461 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6463 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6464 (p : Pattern) (guard : d1329 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6463 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6465 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6466 (p : Pattern) (guard : d1332 p = 1) : d179 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d1332, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d1332, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6467 (p : Pattern) (guard : d1333 p = 1) : d179 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6468 (p : Pattern) (guard : d1334 p = 1) : d180 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d180, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d1334, d180, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d180, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6467 p hg
    simpa only [d1334, d180, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6469 (p : Pattern) (guard : d1332 p = 1) : d68 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1332, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6470 (p : Pattern) (guard : d1333 p = 1) : d68 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6469 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6471 (p : Pattern) (guard : d0 p = 1) : d181 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6472 (p : Pattern) (guard : d1335 p = 1) : d181 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6473 (p : Pattern) (guard : d1336 p = 1) : d182 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d1336, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6472 p hg
    simpa only [d1336, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6474 (p : Pattern) (guard : d1337 p = 1) : d183 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d183, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d1337, d183, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d183, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d1337, d183, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6475 (p : Pattern) (guard : d1335 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6476 (p : Pattern) (guard : d1338 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6477 (p : Pattern) (guard : d1339 p = 1) : d184 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d1339, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6476 p hg
    simpa only [d1339, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6478 (p : Pattern) (guard : d1340 p = 1) : d185 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d185, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d1340, d185, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d185, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d1340, d185, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6479 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6480 (p : Pattern) (guard : d1332 p = 1) : d186 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1332, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6479 p hg
    simpa only [d1332, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6481 (p : Pattern) (guard : d1333 p = 1) : d186 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6482 (p : Pattern) (guard : d1336 p = 1) : d187 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6481 p hg
    simpa only [d1336, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d1336, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6483 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6484 (p : Pattern) (guard : d1335 p = 1) : d188 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6483 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6485 (p : Pattern) (guard : d1338 p = 1) : d189 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1338, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1338, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6486 (p : Pattern) (guard : d1339 p = 1) : d190 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1339, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6485 p hg
    simpa only [d1339, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6487 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6488 (p : Pattern) (guard : d1335 p = 1) : d191 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6489 (p : Pattern) (guard : d1338 p = 1) : d192 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d1338, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1338, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6490 (p : Pattern) (guard : d1341 p = 1) : d193 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6489 p hg
    simpa only [d1341, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1341, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6491 (p : Pattern) (guard : d1342 p = 1) : d194 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6486 p hg
    simpa only [d1342, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6490 p hg
    simpa only [d1342, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6492 (p : Pattern) (guard : d1343 p = 1) : d195 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d195, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d1343, d195, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d195, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6491 p hg
    simpa only [d1343, d195, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6493 (p : Pattern) (guard : d1329 p = 1) : d107 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d1329, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1329, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6494 (p : Pattern) (guard : d1330 p = 1) : d108 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d1330, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d1330, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6495 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6496 (p : Pattern) (guard : d1332 p = 1) : d111 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6497 (p : Pattern) (guard : d1333 p = 1) : d112 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6494 p hg
    simpa only [d1333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d1333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6498 (p : Pattern) (guard : d1334 p = 1) : d113 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d113, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d1334, d113, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d113, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d1334, d113, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6499 (p : Pattern) (guard : d1329 p = 1) : d114 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d1329, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1329, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6500 (p : Pattern) (guard : d1330 p = 1) : d115 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1330, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d1330, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6501 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6502 (p : Pattern) (guard : d1332 p = 1) : d117 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1332, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d1332, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6503 (p : Pattern) (guard : d1333 p = 1) : d118 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6500 p hg
    simpa only [d1333, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6502 p hg
    simpa only [d1333, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6504 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6505 (p : Pattern) (guard : d1332 p = 1) : d124 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1332, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d1332, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6506 (p : Pattern) (guard : d0 p = 1) : d131 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6507 (p : Pattern) (guard : d1335 p = 1) : d132 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6505 p hg
    simpa only [d1335, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6506 p hg
    simpa only [d1335, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6508 (p : Pattern) (guard : d1336 p = 1) : d133 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6503 p hg
    simpa only [d1336, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d1336, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6509 (p : Pattern) (guard : d1337 p = 1) : d134 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d134, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d1337, d134, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d134, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d1337, d134, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6510 (p : Pattern) (guard : d1309 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6511 (p : Pattern) (guard : d1311 p = 1) : d54 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d1311, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1311, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6512 (p : Pattern) (guard : d1312 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6510 p hg
    simpa only [d1312, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d1312, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6513 (p : Pattern) (guard : d1315 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6512 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6514 (p : Pattern) (guard : d1318 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6513 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6515 (p : Pattern) (guard : d1321 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6514 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6516 (p : Pattern) (guard : d1324 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6517 (p : Pattern) (guard : d1327 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6516 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6518 (p : Pattern) (guard : d1330 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6519 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6520 (p : Pattern) (guard : d1323 p = 1) : d65 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d1323, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d1323, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6521 (p : Pattern) (guard : d1326 p = 1) : d65 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6522 (p : Pattern) (guard : d1329 p = 1) : d65 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6523 (p : Pattern) (guard : d1332 p = 1) : d65 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6524 (p : Pattern) (guard : d1333 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d1333, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d1333, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6525 (p : Pattern) (guard : d1336 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6524 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6526 (p : Pattern) (guard : d1339 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6525 p hg
    simpa only [d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6527 (p : Pattern) (guard : d1340 p = 1) : d199 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d199, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d1340, d199, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d199, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d1340, d199, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6528 (p : Pattern) (guard : d1330 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6529 (p : Pattern) (guard : d1332 p = 1) : d63 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6530 (p : Pattern) (guard : d1333 p = 1) : d64 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6528 p hg
    simpa only [d1333, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d1333, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6531 (p : Pattern) (guard : d1336 p = 1) : d67 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d1336, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6532 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6533 (p : Pattern) (guard : d1332 p = 1) : d142 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d1332, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d1332, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6534 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6535 (p : Pattern) (guard : d1335 p = 1) : d150 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d1335, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d1335, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6536 (p : Pattern) (guard : d1338 p = 1) : d151 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d1338, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6537 (p : Pattern) (guard : d1339 p = 1) : d152 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d1339, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6538 (p : Pattern) (guard : d1341 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6539 (p : Pattern) (guard : d1342 p = 1) : d200 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d1342, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d1342, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6540 (p : Pattern) (guard : d1343 p = 1) : d201 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d201, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6527 p hg
    simpa only [d1343, d201, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d201, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6539 p hg
    simpa only [d1343, d201, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6541 (p : Pattern) (guard : d1334 p = 1) : d67 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d67, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d1334, d67, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d67, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6524 p hg
    simpa only [d1334, d67, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6542 (p : Pattern) (guard : d1336 p = 1) : d71 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d1336, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6543 (p : Pattern) (guard : d1337 p = 1) : d72 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d72, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d1337, d72, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d72, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d1337, d72, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6544 (p : Pattern) (guard : d1339 p = 1) : d73 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d1339, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6545 (p : Pattern) (guard : d1340 p = 1) : d74 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d74, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6543 p hg
    simpa only [d1340, d74, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d74, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d1340, d74, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6546 (p : Pattern) (guard : d0 p = 1) : d69 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6547 (p : Pattern) (guard : d1335 p = 1) : d70 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6469 p hg
    simpa only [d1335, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d1335, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6548 (p : Pattern) (guard : d1338 p = 1) : d71 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6547 p hg
    simpa only [d1338, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6549 (p : Pattern) (guard : d1339 p = 1) : d72 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d1339, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d1339, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6550 (p : Pattern) (guard : d1341 p = 1) : d73 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d1341, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6551 (p : Pattern) (guard : d1342 p = 1) : d74 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6549 p hg
    simpa only [d1342, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d1342, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6552 (p : Pattern) (guard : d1343 p = 1) : d74 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6545 p hg
    simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6551 p hg
    simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6553 (p : Pattern) (guard : d1342 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6554 (p : Pattern) (guard : d1343 p = 1) : d75 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d75, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6545 p hg
    simpa only [d1343, d75, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d75, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d1343, d75, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6555 (p : Pattern) (guard : d1313 p = 1) : d119 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6341 p hg
    simpa only [d1313, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6512 p hg
    simpa only [d1313, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6556 (p : Pattern) (guard : d1315 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d1315, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d1315, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6557 (p : Pattern) (guard : d1316 p = 1) : d119 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6558 (p : Pattern) (guard : d1315 p = 1) : d119 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d1315, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d1315, d119, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6559 (p : Pattern) (guard : d1317 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d1317, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1317, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6560 (p : Pattern) (guard : d1318 p = 1) : d119 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6561 (p : Pattern) (guard : d1319 p = 1) : d119 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6557 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6562 (p : Pattern) (guard : d1318 p = 1) : d137 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d1318, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d1318, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6563 (p : Pattern) (guard : d1320 p = 1) : d137 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1320, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1320, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6564 (p : Pattern) (guard : d1321 p = 1) : d137 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6565 (p : Pattern) (guard : d1322 p = 1) : d501 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d501, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6561 p hg
    simpa only [d1322, d501, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d501, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6564 p hg
    simpa only [d1322, d501, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6566 (p : Pattern) (guard : d1318 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6567 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6568 (p : Pattern) (guard : d1320 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6569 (p : Pattern) (guard : d1321 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6566 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6570 (p : Pattern) (guard : d1323 p = 1) : d137 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6571 (p : Pattern) (guard : d1324 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6569 p hg
    simpa only [d1324, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d1324, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6572 (p : Pattern) (guard : d1325 p = 1) : d501 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6565 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6573 (p : Pattern) (guard : d1323 p = 1) : d119 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6574 (p : Pattern) (guard : d1326 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6573 p hg
    simpa only [d1326, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1326, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6575 (p : Pattern) (guard : d1327 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6574 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6576 (p : Pattern) (guard : d1328 p = 1) : d501 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6572 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6577 (p : Pattern) (guard : d1317 p = 1) : d125 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d125, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d1317, d125, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d125, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d1317, d125, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6578 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6579 (p : Pattern) (guard : d1320 p = 1) : d125 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6577 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6578 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
