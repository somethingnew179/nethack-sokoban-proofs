/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6580 (p : Pattern) (guard : d1321 p = 1) : d502 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d1321, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d1321, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6581 (p : Pattern) (guard : d0 p = 1) : d143 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6582 (p : Pattern) (guard : d1323 p = 1) : d144 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d1323, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6581 p hg
    simpa only [d1323, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6583 (p : Pattern) (guard : d1324 p = 1) : d503 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d503, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6580 p hg
    simpa only [d1324, d503, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d503, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6582 p hg
    simpa only [d1324, d503, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6584 (p : Pattern) (guard : d1323 p = 1) : d502 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1323, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6578 p hg
    simpa only [d1323, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6585 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6586 (p : Pattern) (guard : d1326 p = 1) : d503 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6584 p hg
    simpa only [d1326, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6585 p hg
    simpa only [d1326, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6587 (p : Pattern) (guard : d1327 p = 1) : d503 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6583 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6586 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6588 (p : Pattern) (guard : d0 p = 1) : d503 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6589 (p : Pattern) (guard : d1329 p = 1) : d503 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6586 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6590 (p : Pattern) (guard : d1330 p = 1) : d503 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6587 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6591 (p : Pattern) (guard : d1331 p = 1) : d504 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6576 p hg
    simpa only [d1331, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6590 p hg
    simpa only [d1331, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6592 (p : Pattern) (guard : d1324 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6569 p hg
    simpa only [d1324, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1324, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6593 (p : Pattern) (guard : d1326 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6573 p hg
    simpa only [d1326, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1326, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6594 (p : Pattern) (guard : d1327 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6592 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6593 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6595 (p : Pattern) (guard : d0 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6596 (p : Pattern) (guard : d1329 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6593 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6595 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6597 (p : Pattern) (guard : d1330 p = 1) : d505 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6594 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6598 (p : Pattern) (guard : d1326 p = 1) : d506 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6584 p hg
    simpa only [d1326, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1326, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6599 (p : Pattern) (guard : d0 p = 1) : d506 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6600 (p : Pattern) (guard : d1329 p = 1) : d506 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6598 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6599 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6601 (p : Pattern) (guard : d1332 p = 1) : d506 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6599 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6602 (p : Pattern) (guard : d1333 p = 1) : d507 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6597 p hg
    simpa only [d1333, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6601 p hg
    simpa only [d1333, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6603 (p : Pattern) (guard : d1334 p = 1) : d508 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d508, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6591 p hg
    simpa only [d1334, d508, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d508, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6602 p hg
    simpa only [d1334, d508, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6604 (p : Pattern) (guard : d1330 p = 1) : d509 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d1330, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6605 (p : Pattern) (guard : d1332 p = 1) : d510 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d1332, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6606 (p : Pattern) (guard : d1333 p = 1) : d511 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6604 p hg
    simpa only [d1333, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6605 p hg
    simpa only [d1333, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6607 (p : Pattern) (guard : d1332 p = 1) : d512 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d1332, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6608 (p : Pattern) (guard : d0 p = 1) : d513 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6609 (p : Pattern) (guard : d1335 p = 1) : d514 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6607 p hg
    simpa only [d1335, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6608 p hg
    simpa only [d1335, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6610 (p : Pattern) (guard : d1336 p = 1) : d515 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6606 p hg
    simpa only [d1336, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6609 p hg
    simpa only [d1336, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6611 (p : Pattern) (guard : d1337 p = 1) : d516 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d516, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6603 p hg
    simpa only [d1337, d516, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d516, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6610 p hg
    simpa only [d1337, d516, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6612 (p : Pattern) (guard : d1339 p = 1) : d517 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6610 p hg
    simpa only [d1339, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6613 (p : Pattern) (guard : d1340 p = 1) : d518 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d518, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6611 p hg
    simpa only [d1340, d518, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d518, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6612 p hg
    simpa only [d1340, d518, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6614 (p : Pattern) (guard : d0 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6615 (p : Pattern) (guard : d1329 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6574 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6614 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6616 (p : Pattern) (guard : d1330 p = 1) : d501 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6617 (p : Pattern) (guard : d1332 p = 1) : d503 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6618 (p : Pattern) (guard : d1333 p = 1) : d504 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6616 p hg
    simpa only [d1333, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6617 p hg
    simpa only [d1333, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6619 (p : Pattern) (guard : d1336 p = 1) : d519 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6618 p hg
    simpa only [d1336, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6620 (p : Pattern) (guard : d1332 p = 1) : d509 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d1332, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6621 (p : Pattern) (guard : d0 p = 1) : d510 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6622 (p : Pattern) (guard : d1335 p = 1) : d511 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6620 p hg
    simpa only [d1335, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6621 p hg
    simpa only [d1335, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6623 (p : Pattern) (guard : d1338 p = 1) : d520 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d1338, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6624 (p : Pattern) (guard : d1339 p = 1) : d521 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d1339, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d1339, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6625 (p : Pattern) (guard : d1341 p = 1) : d522 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d1341, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6626 (p : Pattern) (guard : d1342 p = 1) : d523 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d1342, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d1342, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6627 (p : Pattern) (guard : d1343 p = 1) : d524 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d524, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6613 p hg
    simpa only [d1343, d524, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d524, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d1343, d524, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6628 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare6629 (p : Pattern) (guard : d1233 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (3 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6630 (p : Pattern) (guard : d1309 p = 1) : d3 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d1309, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6631 (p : Pattern) (guard : d1310 p = 1) : d24 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1310, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1310, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1309 p = 1 := by simpa only [d1310, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d1310, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6632 (p : Pattern) (guard : d1311 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (3 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6633 (p : Pattern) (guard : d1312 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d1312, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d1312, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6634 (p : Pattern) (guard : d1313 p = 1) : d24 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6635 (p : Pattern) (guard : d1314 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6346 p hg
    simpa only [d1314, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1314, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6636 (p : Pattern) (guard : d1315 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6637 (p : Pattern) (guard : d1316 p = 1) : d24 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6638 (p : Pattern) (guard : d1233 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare6639 (p : Pattern) (guard : d1311 p = 1) : d3 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6640 (p : Pattern) (guard : d1312 p = 1) : d24 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d1312, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d1312, d24, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6641 (p : Pattern) (guard : d1315 p = 1) : d24 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6640 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6642 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6643 (p : Pattern) (guard : d1317 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6644 (p : Pattern) (guard : d1318 p = 1) : d24 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6641 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6645 (p : Pattern) (guard : d1319 p = 1) : d24 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6646 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6647 (p : Pattern) (guard : d1314 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6358 p hg
    simpa only [d1314, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6646 p hg
    simpa only [d1314, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6648 (p : Pattern) (guard : d0 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6649 (p : Pattern) (guard : d1317 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6647 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6650 (p : Pattern) (guard : d1318 p = 1) : d526 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d1318, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d1318, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6651 (p : Pattern) (guard : d1320 p = 1) : d526 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d1320, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1320, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6652 (p : Pattern) (guard : d1321 p = 1) : d526 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6650 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6653 (p : Pattern) (guard : d1322 p = 1) : d527 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d527, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6645 p hg
    simpa only [d1322, d527, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d527, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d1322, d527, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6654 (p : Pattern) (guard : d1318 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6655 (p : Pattern) (guard : d1320 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6656 (p : Pattern) (guard : d1321 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6657 (p : Pattern) (guard : d0 p = 1) : d526 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6658 (p : Pattern) (guard : d1323 p = 1) : d526 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6657 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6659 (p : Pattern) (guard : d1324 p = 1) : d527 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6656 p hg
    simpa only [d1324, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6658 p hg
    simpa only [d1324, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6660 (p : Pattern) (guard : d1325 p = 1) : d527 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6653 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6661 (p : Pattern) (guard : d1323 p = 1) : d24 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6662 (p : Pattern) (guard : d1326 p = 1) : d527 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d1326, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6657 p hg
    simpa only [d1326, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6663 (p : Pattern) (guard : d1327 p = 1) : d527 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6664 (p : Pattern) (guard : d1328 p = 1) : d527 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6660 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6665 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6666 (p : Pattern) (guard : d1314 p = 1) : d25 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d25, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d1314, d25, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d25, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6665 p hg
    simpa only [d1314, d25, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6667 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6668 (p : Pattern) (guard : d1317 p = 1) : d25 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6669 (p : Pattern) (guard : d1320 p = 1) : d25 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6668 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6670 (p : Pattern) (guard : d1321 p = 1) : d26 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d1321, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6669 p hg
    simpa only [d1321, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6671 (p : Pattern) (guard : d0 p = 1) : d529 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6672 (p : Pattern) (guard : d1323 p = 1) : d530 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d1323, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6671 p hg
    simpa only [d1323, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6673 (p : Pattern) (guard : d1324 p = 1) : d531 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d531, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d1324, d531, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d531, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d1324, d531, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6674 (p : Pattern) (guard : d1323 p = 1) : d26 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d1323, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d1323, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6675 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6676 (p : Pattern) (guard : d1326 p = 1) : d531 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d1326, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6675 p hg
    simpa only [d1326, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6677 (p : Pattern) (guard : d1327 p = 1) : d531 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6678 (p : Pattern) (guard : d0 p = 1) : d531 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6679 (p : Pattern) (guard : d1329 p = 1) : d531 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6678 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6680 (p : Pattern) (guard : d1330 p = 1) : d531 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6677 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6681 (p : Pattern) (guard : d1331 p = 1) : d532 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6664 p hg
    simpa only [d1331, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d1331, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6682 (p : Pattern) (guard : d1320 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6683 (p : Pattern) (guard : d1323 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6682 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6684 (p : Pattern) (guard : d1324 p = 1) : d533 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6656 p hg
    simpa only [d1324, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6683 p hg
    simpa only [d1324, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6685 (p : Pattern) (guard : d1326 p = 1) : d533 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d1326, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1326, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6686 (p : Pattern) (guard : d1327 p = 1) : d533 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6685 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6687 (p : Pattern) (guard : d0 p = 1) : d536 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6688 (p : Pattern) (guard : d1329 p = 1) : d537 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6685 p hg
    simpa only [d1329, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d1329, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6689 (p : Pattern) (guard : d1330 p = 1) : d538 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6686 p hg
    simpa only [d1330, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6688 p hg
    simpa only [d1330, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6690 (p : Pattern) (guard : d0 p = 1) : d539 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6691 (p : Pattern) (guard : d1326 p = 1) : d540 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d1326, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6690 p hg
    simpa only [d1326, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6692 (p : Pattern) (guard : d0 p = 1) : d540 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6693 (p : Pattern) (guard : d1329 p = 1) : d540 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6692 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6694 (p : Pattern) (guard : d0 p = 1) : d545 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6695 (p : Pattern) (guard : d1332 p = 1) : d546 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6693 p hg
    simpa only [d1332, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6694 p hg
    simpa only [d1332, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6696 (p : Pattern) (guard : d1333 p = 1) : d547 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6689 p hg
    simpa only [d1333, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6695 p hg
    simpa only [d1333, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6697 (p : Pattern) (guard : d1334 p = 1) : d548 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d548, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d1334, d548, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d548, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d1334, d548, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6698 (p : Pattern) (guard : d1326 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6683 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6699 (p : Pattern) (guard : d1329 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6698 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6700 (p : Pattern) (guard : d1330 p = 1) : d549 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d1330, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d1330, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6701 (p : Pattern) (guard : d1332 p = 1) : d550 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d1332, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6690 p hg
    simpa only [d1332, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6702 (p : Pattern) (guard : d1333 p = 1) : d551 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d1333, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6701 p hg
    simpa only [d1333, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6703 (p : Pattern) (guard : d1332 p = 1) : d552 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6688 p hg
    simpa only [d1332, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1332, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6704 (p : Pattern) (guard : d0 p = 1) : d553 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6705 (p : Pattern) (guard : d1335 p = 1) : d554 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6703 p hg
    simpa only [d1335, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6704 p hg
    simpa only [d1335, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6706 (p : Pattern) (guard : d1336 p = 1) : d555 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6702 p hg
    simpa only [d1336, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d1336, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6707 (p : Pattern) (guard : d1337 p = 1) : d556 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d556, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6697 p hg
    simpa only [d1337, d556, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d556, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d1337, d556, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6708 (p : Pattern) (guard : d1332 p = 1) : d525 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6709 (p : Pattern) (guard : d1335 p = 1) : d557 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6708 p hg
    simpa only [d1335, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6690 p hg
    simpa only [d1335, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6710 (p : Pattern) (guard : d0 p = 1) : d557 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6711 (p : Pattern) (guard : d1338 p = 1) : d557 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6712 (p : Pattern) (guard : d1339 p = 1) : d558 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d1339, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6711 p hg
    simpa only [d1339, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6713 (p : Pattern) (guard : d1340 p = 1) : d559 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d559, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6707 p hg
    simpa only [d1340, d559, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d559, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d1340, d559, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6714 (p : Pattern) (guard : d0 p = 1) : d561 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6715 (p : Pattern) (guard : d1329 p = 1) : d562 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d1329, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d1329, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6716 (p : Pattern) (guard : d1330 p = 1) : d563 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d1330, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d1330, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6717 (p : Pattern) (guard : d0 p = 1) : d567 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6718 (p : Pattern) (guard : d1332 p = 1) : d568 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d1332, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6717 p hg
    simpa only [d1332, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6719 (p : Pattern) (guard : d1333 p = 1) : d569 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6716 p hg
    simpa only [d1333, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6718 p hg
    simpa only [d1333, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
