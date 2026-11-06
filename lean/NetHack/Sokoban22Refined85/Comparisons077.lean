/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10780 (p : Pattern) (guard : d4148 p = 1) : d1451 p ≤ (0 : Int) + d1338 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3818 p hg
    simpa only [d1451, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d1451, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10781 (p : Pattern) (guard : d4148 p = 1) : d1452 p ≤ (0 : Int) + d1339 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10780 p hg
    simpa only [d1452, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d1452, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10782 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10781 p hg
    simpa only [d1456, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1456, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10783 (p : Pattern) (guard : d4148 p = 1) : d1464 p ≤ (0 : Int) + d1341 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1464, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10782 p hg
    simpa only [d1464, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1464, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1464, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10784 (p : Pattern) (guard : d4148 p = 1) : d1465 p ≤ (0 : Int) + d1342 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1465, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10779 p hg
    simpa only [d1465, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1465, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1465, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10785 (p : Pattern) (guard : d4148 p = 1) : d1466 p ≤ (0 : Int) + d1343 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1466, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10762 p hg
    simpa only [d1466, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1466, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d1466, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10786 (p : Pattern) (guard : d4148 p = 1) : d1467 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1467, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1467, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1467, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10785 p hg
    simpa only [d1467, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10787 (p : Pattern) (guard : d4148 p = 1) : d1468 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1468, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10729 p hg
    simpa only [d1468, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1468, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10786 p hg
    simpa only [d1468, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10788 (p : Pattern) (guard : d4148 p = 1) : d1469 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10789 (p : Pattern) (guard : d4148 p = 1) : d1470 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1470, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10788 p hg
    simpa only [d1470, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1470, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1470, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10790 (p : Pattern) (guard : d4148 p = 1) : d1100 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8299 p hg
    simpa only [d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10791 (p : Pattern) (guard : d4148 p = 1) : d1101 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10790 p hg
    simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10792 (p : Pattern) (guard : d4148 p = 1) : d1471 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1471, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10789 p hg
    simpa only [d1471, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1471, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10791 p hg
    simpa only [d1471, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10793 (p : Pattern) (guard : d4148 p = 1) : d1472 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1472, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10723 p hg
    simpa only [d1472, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1472, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10792 p hg
    simpa only [d1472, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10794 (p : Pattern) (guard : d4148 p = 1) : d1473 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1473, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10721 p hg
    simpa only [d1473, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1473, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10793 p hg
    simpa only [d1473, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10795 (p : Pattern) (guard : d4148 p = 1) : d1472 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1472, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10685 p hg
    simpa only [d1472, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1472, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10792 p hg
    simpa only [d1472, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10796 (p : Pattern) (guard : d4148 p = 1) : d1474 p ≤ (0 : Int) + d1354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1474, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10795 p hg
    simpa only [d1474, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1474, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1474, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10797 (p : Pattern) (guard : d4148 p = 1) : d1475 p ≤ (0 : Int) + d1355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1475, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10794 p hg
    simpa only [d1475, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1475, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10796 p hg
    simpa only [d1475, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10798 (p : Pattern) (guard : d4148 p = 1) : d1476 p ≤ (0 : Int) + d1356 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1476, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10715 p hg
    simpa only [d1476, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1476, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10797 p hg
    simpa only [d1476, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10799 (p : Pattern) (guard : d4148 p = 1) : d1477 p ≤ (0 : Int) + d1357 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1477, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1477, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1477, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10798 p hg
    simpa only [d1477, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10800 (p : Pattern) (guard : d4148 p = 1) : d1453 p ≤ (0 : Int) + d1358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d1453, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1453, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10801 (p : Pattern) (guard : d4148 p = 1) : d1460 p ≤ (0 : Int) + d1359 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1460, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10800 p hg
    simpa only [d1460, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1460, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10769 p hg
    simpa only [d1460, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10802 (p : Pattern) (guard : d4148 p = 1) : d1461 p ≤ (0 : Int) + d1360 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1461, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10801 p hg
    simpa only [d1461, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1461, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10740 p hg
    simpa only [d1461, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10803 (p : Pattern) (guard : d4148 p = 1) : d1462 p ≤ (0 : Int) + d1361 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1462, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10734 p hg
    simpa only [d1462, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1462, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10802 p hg
    simpa only [d1462, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10804 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1362 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10747 p hg
    simpa only [d1456, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1456, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10805 (p : Pattern) (guard : d4148 p = 1) : d1463 p ≤ (0 : Int) + d1363 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1463, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10803 p hg
    simpa only [d1463, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1463, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10804 p hg
    simpa only [d1463, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10806 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1364 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10756 p hg
    simpa only [d1456, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1456, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10807 (p : Pattern) (guard : d4148 p = 1) : d1458 p ≤ (0 : Int) + d1365 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1458, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10806 p hg
    simpa only [d1458, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1458, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1458, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10808 (p : Pattern) (guard : d4148 p = 1) : d1478 p ≤ (0 : Int) + d1366 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1478, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10805 p hg
    simpa only [d1478, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1478, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10807 p hg
    simpa only [d1478, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10809 (p : Pattern) (guard : d4148 p = 1) : d1479 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1479, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d1479, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1479, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1479, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10810 (p : Pattern) (guard : d4148 p = 1) : d1480 p ≤ (0 : Int) + d1368 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1480, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d1480, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1480, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10809 p hg
    simpa only [d1480, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10811 (p : Pattern) (guard : d4148 p = 1) : d1481 p ≤ (0 : Int) + d1371 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1481, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8323 p hg
    simpa only [d1481, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1481, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d1481, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10812 (p : Pattern) (guard : d4148 p = 1) : d1482 p ≤ (0 : Int) + d1373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1482, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10811 p hg
    simpa only [d1482, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1482, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d1482, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10813 (p : Pattern) (guard : d4148 p = 1) : d1483 p ≤ (0 : Int) + d1374 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1483, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10810 p hg
    simpa only [d1483, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1483, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10812 p hg
    simpa only [d1483, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10814 (p : Pattern) (guard : d4148 p = 1) : d1124 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10815 (p : Pattern) (guard : d4148 p = 1) : d1484 p ≤ (0 : Int) + d1333 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1484, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10775 p hg
    simpa only [d1484, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1484, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10814 p hg
    simpa only [d1484, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10816 (p : Pattern) (guard : d4148 p = 1) : d1485 p ≤ (0 : Int) + d1376 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1485, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d1485, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1485, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10052 p hg
    simpa only [d1485, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10817 (p : Pattern) (guard : d4148 p = 1) : d1129 p ≤ (0 : Int) + d1377 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8336 p hg
    simpa only [d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10818 (p : Pattern) (guard : d4148 p = 1) : d1486 p ≤ (0 : Int) + d1378 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1486, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10816 p hg
    simpa only [d1486, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1486, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10817 p hg
    simpa only [d1486, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10819 (p : Pattern) (guard : d4148 p = 1) : d1487 p ≤ (0 : Int) + d1379 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1487, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10815 p hg
    simpa only [d1487, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1487, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10818 p hg
    simpa only [d1487, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10820 (p : Pattern) (guard : d4148 p = 1) : d1488 p ≤ (0 : Int) + d1380 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1488, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10813 p hg
    simpa only [d1488, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1488, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10819 p hg
    simpa only [d1488, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10821 (p : Pattern) (guard : d4148 p = 1) : d1489 p ≤ (0 : Int) + d1381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1489, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d1489, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1489, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d1489, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10822 (p : Pattern) (guard : d4148 p = 1) : d1490 p ≤ (0 : Int) + d1382 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1490, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8343 p hg
    simpa only [d1490, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1490, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d1490, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10823 (p : Pattern) (guard : d4148 p = 1) : d1491 p ≤ (0 : Int) + d1383 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1491, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10821 p hg
    simpa only [d1491, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1491, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10822 p hg
    simpa only [d1491, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10824 (p : Pattern) (guard : d4148 p = 1) : d1492 p ≤ (0 : Int) + d1384 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1492, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10823 p hg
    simpa only [d1492, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1492, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d1492, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10825 (p : Pattern) (guard : d4148 p = 1) : d1493 p ≤ (0 : Int) + d1386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1493, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d1493, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1493, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10065 p hg
    simpa only [d1493, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10826 (p : Pattern) (guard : d4148 p = 1) : d1138 p ≤ (0 : Int) + d1387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8349 p hg
    simpa only [d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10827 (p : Pattern) (guard : d4148 p = 1) : d1494 p ≤ (0 : Int) + d1388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1494, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10825 p hg
    simpa only [d1494, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1494, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10826 p hg
    simpa only [d1494, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10828 (p : Pattern) (guard : d4148 p = 1) : d1140 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8352 p hg
    simpa only [d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10829 (p : Pattern) (guard : d4148 p = 1) : d1141 p ≤ (0 : Int) + d1389 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10828 p hg
    simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10830 (p : Pattern) (guard : d4148 p = 1) : d1495 p ≤ (0 : Int) + d1390 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1495, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10827 p hg
    simpa only [d1495, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1495, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10829 p hg
    simpa only [d1495, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10831 (p : Pattern) (guard : d4148 p = 1) : d1496 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1496, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d1496, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1496, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10830 p hg
    simpa only [d1496, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10832 (p : Pattern) (guard : d4148 p = 1) : d1497 p ≤ (0 : Int) + d1392 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1497, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10820 p hg
    simpa only [d1497, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1497, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10831 p hg
    simpa only [d1497, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10833 (p : Pattern) (guard : d4148 p = 1) : d1498 p ≤ (0 : Int) + d1393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1498, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10831 p hg
    simpa only [d1498, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1498, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1498, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10834 (p : Pattern) (guard : d4148 p = 1) : d1499 p ≤ (0 : Int) + d1394 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1499, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10832 p hg
    simpa only [d1499, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1499, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10833 p hg
    simpa only [d1499, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10835 (p : Pattern) (guard : d4148 p = 1) : d1500 p ≤ (0 : Int) + d1395 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1500, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10808 p hg
    simpa only [d1500, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1500, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10834 p hg
    simpa only [d1500, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10836 (p : Pattern) (guard : d4148 p = 1) : d1501 p ≤ (0 : Int) + d1396 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1501, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1501, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1501, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10835 p hg
    simpa only [d1501, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10837 (p : Pattern) (guard : d4148 p = 1) : d1502 p ≤ (0 : Int) + d1397 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1502, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10799 p hg
    simpa only [d1502, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1502, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10836 p hg
    simpa only [d1502, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10838 (p : Pattern) (guard : d4148 p = 1) : d1503 p ≤ (0 : Int) + d1398 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1503, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10787 p hg
    simpa only [d1503, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1503, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10837 p hg
    simpa only [d1503, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10839 (p : Pattern) (guard : d4147 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare10840 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10841 (p : Pattern) (guard : d4765 p = 1) : d22 p ≤ (0 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10839 p hg
    simpa only [d4765, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10840 p hg
    simpa only [d4765, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10842 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10843 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d9 p := by
  change (2 : Int) ≤ (0 : Int) + 9
  decide
theorem compare10844 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10845 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10846 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10845 p hg
    simpa only [d32, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10847 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10846 p hg
    simpa only [d33, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10848 (p : Pattern) (guard : d4147 p = 1) : d950 p ≤ (0 : Int) + d26 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10842 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10847 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10849 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10850 (p : Pattern) (guard : d4765 p = 1) : d1399 p ≤ (0 : Int) + d26 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10848 p hg
    simpa only [d4765, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10849 p hg
    simpa only [d4765, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10851 (p : Pattern) (guard : d4765 p = 1) : d1400 p ≤ (0 : Int) + d4854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1400, d4854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1400, d4854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1400, d4854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10850 p hg
    simpa only [d1400, d4854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10852 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10853 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d33, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d33, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10854 (p : Pattern) (guard : d4147 p = 1) : d33 p ≤ (0 : Int) + d42 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10852 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10853 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10855 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10856 (p : Pattern) (guard : d4765 p = 1) : d1401 p ≤ (0 : Int) + d42 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10854 p hg
    simpa only [d4765, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10855 p hg
    simpa only [d4765, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10857 (p : Pattern) (guard : d0 p = 1) : d46 p ≤ (0 : Int) + d48 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10858 (p : Pattern) (guard : d4147 p = 1) : d47 p ≤ (0 : Int) + d48 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10857 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10859 (p : Pattern) (guard : d0 p = 1) : d49 p ≤ (0 : Int) + d48 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10860 (p : Pattern) (guard : d4765 p = 1) : d50 p ≤ (0 : Int) + d48 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10858 p hg
    simpa only [d4765, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10859 p hg
    simpa only [d4765, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10861 (p : Pattern) (guard : d4765 p = 1) : d1402 p ≤ (0 : Int) + d4855 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1402, d4855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10856 p hg
    simpa only [d1402, d4855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1402, d4855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10860 p hg
    simpa only [d1402, d4855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10862 (p : Pattern) (guard : d4765 p = 1) : d1403 p ≤ (0 : Int) + d4856 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1403, d4856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10851 p hg
    simpa only [d1403, d4856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1403, d4856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10861 p hg
    simpa only [d1403, d4856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10863 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10864 (p : Pattern) (guard : d4147 p = 1) : d54 p ≤ (0 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10863 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10865 (p : Pattern) (guard : d0 p = 1) : d1165 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10866 (p : Pattern) (guard : d4765 p = 1) : d1404 p ≤ (0 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d4765, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10865 p hg
    simpa only [d4765, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10867 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10868 (p : Pattern) (guard : d1 p = 1) : d795 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d795, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d795, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d795, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare940 p hg
    simpa only [d795, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10869 (p : Pattern) (guard : d4147 p = 1) : d796 p ≤ (0 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10867 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10868 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10870 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10871 (p : Pattern) (guard : d4765 p = 1) : d1405 p ≤ (0 : Int) + d62 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10869 p hg
    simpa only [d4765, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d4765, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10872 (p : Pattern) (guard : d4765 p = 1) : d1406 p ≤ (0 : Int) + d4857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1406, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d1406, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1406, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10871 p hg
    simpa only [d1406, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10873 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10874 (p : Pattern) (guard : d1 p = 1) : d795 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d795, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d795, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d795, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d795, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10875 (p : Pattern) (guard : d4147 p = 1) : d796 p ≤ (0 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10873 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10874 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10876 (p : Pattern) (guard : d0 p = 1) : d1171 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10877 (p : Pattern) (guard : d4765 p = 1) : d1407 p ≤ (0 : Int) + d66 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10875 p hg
    simpa only [d4765, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10876 p hg
    simpa only [d4765, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10878 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10879 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d173, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d173, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10880 (p : Pattern) (guard : d4147 p = 1) : d176 p ≤ (0 : Int) + d72 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10878 p hg
    simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10879 p hg
    simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10881 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (0 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10882 (p : Pattern) (guard : d4765 p = 1) : d177 p ≤ (0 : Int) + d72 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10880 p hg
    simpa only [d4765, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10881 p hg
    simpa only [d4765, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10883 (p : Pattern) (guard : d4765 p = 1) : d1408 p ≤ (0 : Int) + d4858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1408, d4858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10877 p hg
    simpa only [d1408, d4858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1408, d4858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10882 p hg
    simpa only [d1408, d4858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10884 (p : Pattern) (guard : d4765 p = 1) : d1409 p ≤ (0 : Int) + d4859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1409, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10872 p hg
    simpa only [d1409, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1409, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1409, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10885 (p : Pattern) (guard : d4765 p = 1) : d1410 p ≤ (0 : Int) + d4860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1410, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10862 p hg
    simpa only [d1410, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1410, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1410, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10886 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10845 p hg
    simpa only [d53, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10846 p hg
    simpa only [d53, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10887 (p : Pattern) (guard : d4147 p = 1) : d54 p ≤ (0 : Int) + d26 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10842 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10886 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10888 (p : Pattern) (guard : d4765 p = 1) : d1411 p ≤ (0 : Int) + d26 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10887 p hg
    simpa only [d4765, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10849 p hg
    simpa only [d4765, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10889 (p : Pattern) (guard : d4765 p = 1) : d1412 p ≤ (0 : Int) + d4854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1412, d4854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1412, d4854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1412, d4854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10888 p hg
    simpa only [d1412, d4854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10890 (p : Pattern) (guard : d4147 p = 1) : d53 p ≤ (0 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10867 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10891 (p : Pattern) (guard : d4765 p = 1) : d1413 p ≤ (0 : Int) + d62 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10890 p hg
    simpa only [d4765, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d4765, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10892 (p : Pattern) (guard : d4765 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare10893 (p : Pattern) (guard : d4765 p = 1) : d1414 p ≤ (0 : Int) + d4689 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1414, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10891 p hg
    simpa only [d1414, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1414, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1414, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10894 (p : Pattern) (guard : d4765 p = 1) : d1415 p ≤ (0 : Int) + d4861 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1415, d4861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10889 p hg
    simpa only [d1415, d4861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1415, d4861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10893 p hg
    simpa only [d1415, d4861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10895 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10896 (p : Pattern) (guard : d4765 p = 1) : d1416 p ≤ (0 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d4765, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10895 p hg
    simpa only [d4765, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10897 (p : Pattern) (guard : d4147 p = 1) : d808 p ≤ (0 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10867 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10898 (p : Pattern) (guard : d4765 p = 1) : d1417 p ≤ (0 : Int) + d62 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d4765, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d4765, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10899 (p : Pattern) (guard : d4765 p = 1) : d1418 p ≤ (0 : Int) + d4857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1418, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10896 p hg
    simpa only [d1418, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1418, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1418, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10900 (p : Pattern) (guard : d4147 p = 1) : d808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10901 (p : Pattern) (guard : d4765 p = 1) : d972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10900 p hg
    simpa only [d4765, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10902 (p : Pattern) (guard : d4765 p = 1) : d974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10901 p hg
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10903 (p : Pattern) (guard : d4765 p = 1) : d1419 p ≤ (0 : Int) + d4862 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1419, d4862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10899 p hg
    simpa only [d1419, d4862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1419, d4862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10902 p hg
    simpa only [d1419, d4862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10904 (p : Pattern) (guard : d4765 p = 1) : d1420 p ≤ (0 : Int) + d4863 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1420, d4863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1420, d4863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1420, d4863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10903 p hg
    simpa only [d1420, d4863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10905 (p : Pattern) (guard : d4765 p = 1) : d1421 p ≤ (0 : Int) + d4864 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1421, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10885 p hg
    simpa only [d1421, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1421, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1421, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10906 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10907 (p : Pattern) (guard : d4147 p = 1) : d89 p ≤ (0 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10906 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10908 (p : Pattern) (guard : d4765 p = 1) : d90 p ≤ (0 : Int) + d62 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10907 p hg
    simpa only [d4765, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d4765, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10909 (p : Pattern) (guard : d4147 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10910 (p : Pattern) (guard : d4765 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10909 p hg
    simpa only [d4765, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10911 (p : Pattern) (guard : d4765 p = 1) : d92 p ≤ (0 : Int) + d4689 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d92, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10908 p hg
    simpa only [d92, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d92, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d92, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10912 (p : Pattern) (guard : d4765 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10913 (p : Pattern) (guard : d4765 p = 1) : d94 p ≤ (0 : Int) + d4690 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d94, d4690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10911 p hg
    simpa only [d94, d4690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d94, d4690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10912 p hg
    simpa only [d94, d4690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10914 (p : Pattern) (guard : d4765 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10912 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10915 (p : Pattern) (guard : d4765 p = 1) : d96 p ≤ (0 : Int) + d4691 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d96, d4691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10913 p hg
    simpa only [d96, d4691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d96, d4691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d96, d4691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10916 (p : Pattern) (guard : d4765 p = 1) : d1422 p ≤ (0 : Int) + d4865 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1422, d4865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1422, d4865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1422, d4865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10915 p hg
    simpa only [d1422, d4865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10917 (p : Pattern) (guard : d4765 p = 1) : d1423 p ≤ (0 : Int) + d4866 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1423, d4866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10905 p hg
    simpa only [d1423, d4866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1423, d4866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10916 p hg
    simpa only [d1423, d4866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10918 (p : Pattern) (guard : d4765 p = 1) : d1424 p ≤ (0 : Int) + d4857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1424, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10896 p hg
    simpa only [d1424, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1424, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10871 p hg
    simpa only [d1424, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10919 (p : Pattern) (guard : d4765 p = 1) : d1425 p ≤ (0 : Int) + d4859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1425, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10918 p hg
    simpa only [d1425, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1425, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1425, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
