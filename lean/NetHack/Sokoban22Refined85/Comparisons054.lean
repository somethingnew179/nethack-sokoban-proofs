/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7560 (p : Pattern) (guard : d4670 p = 1) : d906 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d906, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7555 p hg
    simpa only [d906, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d906, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7559 p hg
    simpa only [d906, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7561 (p : Pattern) (guard : d4670 p = 1) : d907 p ≤ (0 : Int) + d1473 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d907, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d907, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d907, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7560 p hg
    simpa only [d907, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7562 (p : Pattern) (guard : d4670 p = 1) : d908 p ≤ (0 : Int) + d1474 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d908, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7560 p hg
    simpa only [d908, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d908, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d908, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7563 (p : Pattern) (guard : d4670 p = 1) : d909 p ≤ (0 : Int) + d1475 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d909, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7561 p hg
    simpa only [d909, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d909, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7562 p hg
    simpa only [d909, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7564 (p : Pattern) (guard : d4670 p = 1) : d910 p ≤ (0 : Int) + d1476 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d910, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7490 p hg
    simpa only [d910, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d910, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7563 p hg
    simpa only [d910, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7565 (p : Pattern) (guard : d4670 p = 1) : d911 p ≤ (0 : Int) + d1477 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d911, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d911, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d911, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7564 p hg
    simpa only [d911, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7566 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7567 (p : Pattern) (guard : d4395 p = 1) : d212 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d212, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d212, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d212, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7566 p hg
    simpa only [d4395, d212, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7568 (p : Pattern) (guard : d4670 p = 1) : d912 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d912, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d4670, d912, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d912, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d4670, d912, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7569 (p : Pattern) (guard : d4670 p = 1) : d913 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d913, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7568 p hg
    simpa only [d913, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d913, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d913, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7570 (p : Pattern) (guard : d4670 p = 1) : d914 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d914, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d914, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d914, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7569 p hg
    simpa only [d914, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7571 (p : Pattern) (guard : d4670 p = 1) : d915 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d915, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d4670, d915, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d915, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d4670, d915, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7572 (p : Pattern) (guard : d4670 p = 1) : d916 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d916, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7571 p hg
    simpa only [d916, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d916, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d916, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7573 (p : Pattern) (guard : d4670 p = 1) : d917 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d917, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7520 p hg
    simpa only [d917, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d917, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7572 p hg
    simpa only [d917, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7574 (p : Pattern) (guard : d4670 p = 1) : d918 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d918, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7570 p hg
    simpa only [d918, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d918, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7573 p hg
    simpa only [d918, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7575 (p : Pattern) (guard : d4670 p = 1) : d919 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d919, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7529 p hg
    simpa only [d919, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d919, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7572 p hg
    simpa only [d919, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7576 (p : Pattern) (guard : d4670 p = 1) : d920 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d920, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7575 p hg
    simpa only [d920, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d920, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d920, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7577 (p : Pattern) (guard : d4670 p = 1) : d921 p ≤ (0 : Int) + d1478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d921, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7574 p hg
    simpa only [d921, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d921, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7576 p hg
    simpa only [d921, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7578 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7579 (p : Pattern) (guard : d4670 p = 1) : d884 p ≤ (0 : Int) + d1480 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d884, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d884, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d884, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7578 p hg
    simpa only [d4670, d884, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7580 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7581 (p : Pattern) (guard : d4395 p = 1) : d922 p ≤ (0 : Int) + d1481 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d922, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d922, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d922, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7580 p hg
    simpa only [d4395, d922, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7582 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d279 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7583 (p : Pattern) (guard : d4670 p = 1) : d923 p ≤ (0 : Int) + d1482 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d923, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7581 p hg
    simpa only [d4670, d923, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d923, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7582 p hg
    simpa only [d4670, d923, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7584 (p : Pattern) (guard : d4670 p = 1) : d924 p ≤ (0 : Int) + d1483 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d924, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7579 p hg
    simpa only [d924, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d924, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7583 p hg
    simpa only [d924, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7585 (p : Pattern) (guard : d4670 p = 1) : d915 p ≤ (0 : Int) + d1484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d915, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d4670, d915, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d915, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d4670, d915, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7586 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d1375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7587 (p : Pattern) (guard : d4395 p = 1) : d926 p ≤ (0 : Int) + d1485 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d926, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d926, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d926, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d4395, d926, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7588 (p : Pattern) (guard : d4670 p = 1) : d927 p ≤ (0 : Int) + d1486 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d927, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7587 p hg
    simpa only [d4670, d927, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d927, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6640 p hg
    simpa only [d4670, d927, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7589 (p : Pattern) (guard : d4670 p = 1) : d928 p ≤ (0 : Int) + d1487 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d928, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7585 p hg
    simpa only [d928, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d928, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7588 p hg
    simpa only [d928, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7590 (p : Pattern) (guard : d4670 p = 1) : d929 p ≤ (0 : Int) + d1488 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d929, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7584 p hg
    simpa only [d929, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d929, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7589 p hg
    simpa only [d929, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7591 (p : Pattern) (guard : d0 p = 1) : d241 p ≤ (0 : Int) + d293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7592 (p : Pattern) (guard : d4395 p = 1) : d242 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d242, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d242, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d242, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d4395, d242, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7593 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1490 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7594 (p : Pattern) (guard : d4670 p = 1) : d930 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d930, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7592 p hg
    simpa only [d4670, d930, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d930, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d4670, d930, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7595 (p : Pattern) (guard : d4670 p = 1) : d932 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d932, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7594 p hg
    simpa only [d932, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d932, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d932, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7596 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d1385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7597 (p : Pattern) (guard : d4395 p = 1) : d245 p ≤ (0 : Int) + d1493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d245, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d245, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d245, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7596 p hg
    simpa only [d4395, d245, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7598 (p : Pattern) (guard : d4670 p = 1) : d931 p ≤ (0 : Int) + d1494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d931, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d4670, d931, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d931, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d4670, d931, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7599 (p : Pattern) (guard : d4670 p = 1) : d935 p ≤ (0 : Int) + d1495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d935, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7598 p hg
    simpa only [d935, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d935, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d935, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7600 (p : Pattern) (guard : d4670 p = 1) : d936 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d936, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7595 p hg
    simpa only [d936, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d936, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d936, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7601 (p : Pattern) (guard : d4670 p = 1) : d937 p ≤ (0 : Int) + d1497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d937, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7590 p hg
    simpa only [d937, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d937, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7600 p hg
    simpa only [d937, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7602 (p : Pattern) (guard : d0 p = 1) : d252 p ≤ (0 : Int) + d293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7603 (p : Pattern) (guard : d4395 p = 1) : d253 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d253, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d253, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d253, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7602 p hg
    simpa only [d4395, d253, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7604 (p : Pattern) (guard : d4670 p = 1) : d938 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d938, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7603 p hg
    simpa only [d4670, d938, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d938, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d4670, d938, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7605 (p : Pattern) (guard : d4670 p = 1) : d941 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d941, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7604 p hg
    simpa only [d941, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d941, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d941, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7606 (p : Pattern) (guard : d4670 p = 1) : d942 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d942, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7605 p hg
    simpa only [d942, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d942, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d942, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7607 (p : Pattern) (guard : d4670 p = 1) : d943 p ≤ (0 : Int) + d1498 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d943, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7606 p hg
    simpa only [d943, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d943, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d943, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7608 (p : Pattern) (guard : d4670 p = 1) : d944 p ≤ (0 : Int) + d1499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d944, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7601 p hg
    simpa only [d944, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d944, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7607 p hg
    simpa only [d944, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7609 (p : Pattern) (guard : d4670 p = 1) : d945 p ≤ (0 : Int) + d1500 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d945, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7577 p hg
    simpa only [d945, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d945, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7608 p hg
    simpa only [d945, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7610 (p : Pattern) (guard : d4670 p = 1) : d946 p ≤ (0 : Int) + d1501 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d946, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d946, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d946, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d946, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7611 (p : Pattern) (guard : d4670 p = 1) : d947 p ≤ (0 : Int) + d1502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d947, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7565 p hg
    simpa only [d947, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d947, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7610 p hg
    simpa only [d947, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7612 (p : Pattern) (guard : d4670 p = 1) : d948 p ≤ (0 : Int) + d1503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d948, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7548 p hg
    simpa only [d948, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d948, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7611 p hg
    simpa only [d948, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7613 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7614 (p : Pattern) (guard : d4763 p = 1) : d790 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d790, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5053 p hg
    simpa only [d4763, d790, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d790, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7613 p hg
    simpa only [d4763, d790, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7615 (p : Pattern) (guard : d0 p = 1) : d792 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7616 (p : Pattern) (guard : d4764 p = 1) : d793 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d793, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7614 p hg
    simpa only [d4764, d793, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d793, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7615 p hg
    simpa only [d4764, d793, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7617 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7618 (p : Pattern) (guard : d4763 p = 1) : d794 p ≤ (0 : Int) + d1517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d794, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5080 p hg
    simpa only [d4763, d794, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d794, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d4763, d794, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7619 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d1520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7620 (p : Pattern) (guard : d4764 p = 1) : d801 p ≤ (0 : Int) + d1521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d801, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7618 p hg
    simpa only [d4764, d801, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d801, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d4764, d801, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7621 (p : Pattern) (guard : d4764 p = 1) : d802 p ≤ (0 : Int) + d1522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d802, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7616 p hg
    simpa only [d802, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d802, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7620 p hg
    simpa only [d802, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7622 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7623 (p : Pattern) (guard : d4763 p = 1) : d803 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d803, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d4763, d803, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d803, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7622 p hg
    simpa only [d4763, d803, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7624 (p : Pattern) (guard : d0 p = 1) : d805 p ≤ (0 : Int) + d1523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7625 (p : Pattern) (guard : d4764 p = 1) : d806 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d806, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7623 p hg
    simpa only [d4764, d806, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d806, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d4764, d806, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7626 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7627 (p : Pattern) (guard : d4763 p = 1) : d807 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d807, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d4763, d807, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d807, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7626 p hg
    simpa only [d4763, d807, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7628 (p : Pattern) (guard : d0 p = 1) : d811 p ≤ (0 : Int) + d1525 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7629 (p : Pattern) (guard : d4764 p = 1) : d812 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d812, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7627 p hg
    simpa only [d4764, d812, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d812, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7628 p hg
    simpa only [d4764, d812, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7630 (p : Pattern) (guard : d4764 p = 1) : d813 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d813, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7625 p hg
    simpa only [d813, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d813, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d813, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7631 (p : Pattern) (guard : d4764 p = 1) : d814 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d814, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7621 p hg
    simpa only [d814, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d814, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7630 p hg
    simpa only [d814, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7632 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7633 (p : Pattern) (guard : d4763 p = 1) : d815 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d815, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d4763, d815, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d815, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7632 p hg
    simpa only [d4763, d815, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7634 (p : Pattern) (guard : d4764 p = 1) : d816 p ≤ (0 : Int) + d1532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d816, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d4764, d816, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d816, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d4764, d816, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7635 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7636 (p : Pattern) (guard : d4763 p = 1) : d817 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d817, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d4763, d817, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d817, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7635 p hg
    simpa only [d4763, d817, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7637 (p : Pattern) (guard : d4764 p = 1) : d818 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d818, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7636 p hg
    simpa only [d4764, d818, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d818, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7628 p hg
    simpa only [d4764, d818, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7638 (p : Pattern) (guard : d4764 p = 1) : d819 p ≤ (0 : Int) + d1533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d819, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7634 p hg
    simpa only [d819, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d819, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7637 p hg
    simpa only [d819, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7639 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1536 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7640 (p : Pattern) (guard : d4763 p = 1) : d820 p ≤ (0 : Int) + d1537 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d820, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d4763, d820, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d820, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7639 p hg
    simpa only [d4763, d820, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7641 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d1538 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7642 (p : Pattern) (guard : d4764 p = 1) : d821 p ≤ (0 : Int) + d1539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d821, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7640 p hg
    simpa only [d4764, d821, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d821, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7641 p hg
    simpa only [d4764, d821, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7643 (p : Pattern) (guard : d4763 p = 1) : d93 p ≤ (0 : Int) + d1538 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d4763, d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4763, d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7644 (p : Pattern) (guard : d4764 p = 1) : d95 p ≤ (0 : Int) + d1540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7643 p hg
    simpa only [d4764, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4764, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7645 (p : Pattern) (guard : d4764 p = 1) : d822 p ≤ (0 : Int) + d1541 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d822, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7642 p hg
    simpa only [d822, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d822, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7644 p hg
    simpa only [d822, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7646 (p : Pattern) (guard : d4764 p = 1) : d823 p ≤ (0 : Int) + d1542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d823, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7638 p hg
    simpa only [d823, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d823, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7645 p hg
    simpa only [d823, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7647 (p : Pattern) (guard : d4764 p = 1) : d824 p ≤ (0 : Int) + d1543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d824, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7631 p hg
    simpa only [d824, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d824, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7646 p hg
    simpa only [d824, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7648 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7649 (p : Pattern) (guard : d4763 p = 1) : d825 p ≤ (0 : Int) + d1546 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d825, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5128 p hg
    simpa only [d4763, d825, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d825, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7648 p hg
    simpa only [d4763, d825, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7650 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7651 (p : Pattern) (guard : d4764 p = 1) : d827 p ≤ (0 : Int) + d1547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d827, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7649 p hg
    simpa only [d4764, d827, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d827, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7650 p hg
    simpa only [d4764, d827, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7652 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7653 (p : Pattern) (guard : d4763 p = 1) : d828 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d828, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d4763, d828, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d828, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7652 p hg
    simpa only [d4763, d828, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7654 (p : Pattern) (guard : d4764 p = 1) : d829 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7653 p hg
    simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7655 (p : Pattern) (guard : d4764 p = 1) : d830 p ≤ (0 : Int) + d1548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d830, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7651 p hg
    simpa only [d830, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d830, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7654 p hg
    simpa only [d830, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7656 (p : Pattern) (guard : d4763 p = 1) : d831 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d831, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d4763, d831, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d831, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7460 p hg
    simpa only [d4763, d831, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7657 (p : Pattern) (guard : d4764 p = 1) : d832 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d832, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7656 p hg
    simpa only [d4764, d832, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d832, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d4764, d832, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7658 (p : Pattern) (guard : d4764 p = 1) : d833 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d833, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7657 p hg
    simpa only [d833, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d833, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d833, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7659 (p : Pattern) (guard : d4764 p = 1) : d834 p ≤ (0 : Int) + d1549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d834, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7655 p hg
    simpa only [d834, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d834, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d834, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7660 (p : Pattern) (guard : d4764 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare7661 (p : Pattern) (guard : d4764 p = 1) : d835 p ≤ (0 : Int) + d1550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d835, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d835, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d835, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d835, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7662 (p : Pattern) (guard : d4764 p = 1) : d836 p ≤ (0 : Int) + d1551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d836, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7659 p hg
    simpa only [d836, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d836, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7661 p hg
    simpa only [d836, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7663 (p : Pattern) (guard : d4764 p = 1) : d837 p ≤ (0 : Int) + d1552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d837, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7647 p hg
    simpa only [d837, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d837, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7662 p hg
    simpa only [d837, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7664 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7665 (p : Pattern) (guard : d4763 p = 1) : d838 p ≤ (0 : Int) + d1556 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d838, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d4763, d838, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d838, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7664 p hg
    simpa only [d4763, d838, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7666 (p : Pattern) (guard : d4764 p = 1) : d839 p ≤ (0 : Int) + d1557 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d839, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7665 p hg
    simpa only [d4764, d839, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d839, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7650 p hg
    simpa only [d4764, d839, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7667 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7668 (p : Pattern) (guard : d4763 p = 1) : d840 p ≤ (0 : Int) + d1560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d840, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d4763, d840, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d840, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7667 p hg
    simpa only [d4763, d840, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7669 (p : Pattern) (guard : d4764 p = 1) : d841 p ≤ (0 : Int) + d1561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d841, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7668 p hg
    simpa only [d4764, d841, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d841, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d4764, d841, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7670 (p : Pattern) (guard : d4764 p = 1) : d842 p ≤ (0 : Int) + d1562 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d842, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7666 p hg
    simpa only [d842, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d842, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7669 p hg
    simpa only [d842, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7671 (p : Pattern) (guard : d4763 p = 1) : d843 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d843, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d4763, d843, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d843, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d4763, d843, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7672 (p : Pattern) (guard : d4764 p = 1) : d844 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d844, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7671 p hg
    simpa only [d4764, d844, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d844, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d4764, d844, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7673 (p : Pattern) (guard : d4764 p = 1) : d845 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d845, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7672 p hg
    simpa only [d845, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d845, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d845, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7674 (p : Pattern) (guard : d4764 p = 1) : d846 p ≤ (0 : Int) + d1563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d846, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7670 p hg
    simpa only [d846, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d846, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7673 p hg
    simpa only [d846, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7675 (p : Pattern) (guard : d4764 p = 1) : d847 p ≤ (0 : Int) + d1564 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d847, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7630 p hg
    simpa only [d847, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d847, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7645 p hg
    simpa only [d847, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7676 (p : Pattern) (guard : d4764 p = 1) : d848 p ≤ (0 : Int) + d1565 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d848, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7674 p hg
    simpa only [d848, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d848, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7675 p hg
    simpa only [d848, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7677 (p : Pattern) (guard : d4764 p = 1) : d849 p ≤ (0 : Int) + d1566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d849, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d4764, d849, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d849, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7650 p hg
    simpa only [d4764, d849, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7678 (p : Pattern) (guard : d4764 p = 1) : d850 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7636 p hg
    simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7679 (p : Pattern) (guard : d4764 p = 1) : d851 p ≤ (0 : Int) + d1567 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d851, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7677 p hg
    simpa only [d851, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d851, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7678 p hg
    simpa only [d851, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7680 (p : Pattern) (guard : d4764 p = 1) : d852 p ≤ (0 : Int) + d1568 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d852, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7679 p hg
    simpa only [d852, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d852, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d852, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7681 (p : Pattern) (guard : d4764 p = 1) : d853 p ≤ (0 : Int) + d1569 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d853, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7680 p hg
    simpa only [d853, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d853, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7661 p hg
    simpa only [d853, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7682 (p : Pattern) (guard : d4764 p = 1) : d854 p ≤ (0 : Int) + d1570 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d854, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7676 p hg
    simpa only [d854, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d854, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7681 p hg
    simpa only [d854, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7683 (p : Pattern) (guard : d4764 p = 1) : d855 p ≤ (0 : Int) + d1571 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d855, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d855, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d855, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7682 p hg
    simpa only [d855, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7684 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7685 (p : Pattern) (guard : d4763 p = 1) : d856 p ≤ (0 : Int) + d1576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d856, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d4763, d856, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d856, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7684 p hg
    simpa only [d4763, d856, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7686 (p : Pattern) (guard : d0 p = 1) : d858 p ≤ (0 : Int) + d1578 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7687 (p : Pattern) (guard : d4764 p = 1) : d859 p ≤ (0 : Int) + d1579 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d859, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7685 p hg
    simpa only [d4764, d859, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d859, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7686 p hg
    simpa only [d4764, d859, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7688 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7689 (p : Pattern) (guard : d4763 p = 1) : d860 p ≤ (0 : Int) + d1583 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d860, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d4763, d860, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d860, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7688 p hg
    simpa only [d4763, d860, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7690 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d1586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7691 (p : Pattern) (guard : d4764 p = 1) : d866 p ≤ (0 : Int) + d1587 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d866, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d4764, d866, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d866, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7690 p hg
    simpa only [d4764, d866, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7692 (p : Pattern) (guard : d4764 p = 1) : d867 p ≤ (0 : Int) + d1588 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d867, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7687 p hg
    simpa only [d867, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d867, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7691 p hg
    simpa only [d867, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7693 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7694 (p : Pattern) (guard : d4763 p = 1) : d868 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d868, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d4763, d868, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d868, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d4763, d868, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7695 (p : Pattern) (guard : d0 p = 1) : d870 p ≤ (0 : Int) + d1589 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7696 (p : Pattern) (guard : d4764 p = 1) : d871 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d871, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d4764, d871, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d871, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d4764, d871, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7697 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7698 (p : Pattern) (guard : d4763 p = 1) : d872 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d872, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d4763, d872, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d872, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d4763, d872, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7699 (p : Pattern) (guard : d0 p = 1) : d875 p ≤ (0 : Int) + d1591 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
