/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13720 (p : Pattern) (guard : d4395 p = 1) : d1432 p ≤ (0 : Int) + d1022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1432, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13719 p hg
    simpa only [d1432, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1432, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d1432, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13721 (p : Pattern) (guard : d4395 p = 1) : d1433 p ≤ (0 : Int) + d1023 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1433, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13720 p hg
    simpa only [d1433, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1433, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d1433, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13722 (p : Pattern) (guard : d4395 p = 1) : d1434 p ≤ (0 : Int) + d1024 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1434, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13718 p hg
    simpa only [d1434, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1434, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13721 p hg
    simpa only [d1434, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13723 (p : Pattern) (guard : d4395 p = 1) : d1412 p ≤ (0 : Int) + d1026 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d1412, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d1412, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13724 (p : Pattern) (guard : d4395 p = 1) : d1415 p ≤ (0 : Int) + d1027 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13723 p hg
    simpa only [d1415, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1415, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13725 (p : Pattern) (guard : d4395 p = 1) : d1420 p ≤ (0 : Int) + d1028 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13724 p hg
    simpa only [d1420, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13705 p hg
    simpa only [d1420, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13726 (p : Pattern) (guard : d4395 p = 1) : d1435 p ≤ (0 : Int) + d1029 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1435, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13722 p hg
    simpa only [d1435, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1435, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13725 p hg
    simpa only [d1435, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13727 (p : Pattern) (guard : d4395 p = 1) : d1422 p ≤ (0 : Int) + d1030 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1422, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13678 p hg
    simpa only [d1422, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1422, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13688 p hg
    simpa only [d1422, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13728 (p : Pattern) (guard : d4395 p = 1) : d1436 p ≤ (0 : Int) + d1031 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1436, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d1436, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1436, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d1436, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13729 (p : Pattern) (guard : d4395 p = 1) : d1400 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1400, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1400, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1400, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13691 p hg
    simpa only [d1400, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13730 (p : Pattern) (guard : d4395 p = 1) : d1403 p ≤ (0 : Int) + d1033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1403, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d1403, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1403, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13694 p hg
    simpa only [d1403, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13731 (p : Pattern) (guard : d4395 p = 1) : d1424 p ≤ (0 : Int) + d1034 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1424, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13682 p hg
    simpa only [d1424, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1424, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d1424, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13732 (p : Pattern) (guard : d4395 p = 1) : d1425 p ≤ (0 : Int) + d1035 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1425, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13731 p hg
    simpa only [d1425, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1425, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d1425, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13733 (p : Pattern) (guard : d4395 p = 1) : d1426 p ≤ (0 : Int) + d1036 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1426, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d1426, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1426, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1426, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13734 (p : Pattern) (guard : d4395 p = 1) : d1427 p ≤ (0 : Int) + d1037 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1427, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13733 p hg
    simpa only [d1427, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1427, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13706 p hg
    simpa only [d1427, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13735 (p : Pattern) (guard : d4395 p = 1) : d1428 p ≤ (0 : Int) + d1038 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1428, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13706 p hg
    simpa only [d1428, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1428, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1428, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13736 (p : Pattern) (guard : d4395 p = 1) : d1429 p ≤ (0 : Int) + d1039 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1429, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d1429, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1429, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13735 p hg
    simpa only [d1429, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13737 (p : Pattern) (guard : d4395 p = 1) : d1437 p ≤ (0 : Int) + d1040 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1437, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d1437, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1437, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13736 p hg
    simpa only [d1437, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13738 (p : Pattern) (guard : d4395 p = 1) : d1438 p ≤ (0 : Int) + d1041 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1438, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13713 p hg
    simpa only [d1438, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1438, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13737 p hg
    simpa only [d1438, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13739 (p : Pattern) (guard : d4395 p = 1) : d1439 p ≤ (0 : Int) + d1044 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1439, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d4395, d1439, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1439, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d4395, d1439, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13740 (p : Pattern) (guard : d4395 p = 1) : d1440 p ≤ (0 : Int) + d1045 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1440, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d1440, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1440, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13739 p hg
    simpa only [d1440, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13741 (p : Pattern) (guard : d4395 p = 1) : d1441 p ≤ (0 : Int) + d1046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1441, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1441, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1441, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d4395, d1441, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13742 (p : Pattern) (guard : d4395 p = 1) : d129 p ≤ (0 : Int) + d1047 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d4395, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d4395, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13743 (p : Pattern) (guard : d4395 p = 1) : d1442 p ≤ (0 : Int) + d1048 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1442, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13741 p hg
    simpa only [d1442, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1442, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13742 p hg
    simpa only [d1442, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13744 (p : Pattern) (guard : d4395 p = 1) : d1443 p ≤ (0 : Int) + d1049 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1443, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d1443, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1443, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13743 p hg
    simpa only [d1443, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13745 (p : Pattern) (guard : d4395 p = 1) : d1444 p ≤ (0 : Int) + d1050 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1444, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1444, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1444, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10215 p hg
    simpa only [d4395, d1444, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13746 (p : Pattern) (guard : d4395 p = 1) : d1445 p ≤ (0 : Int) + d1052 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1445, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13745 p hg
    simpa only [d1445, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1445, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1445, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13747 (p : Pattern) (guard : d4395 p = 1) : d1446 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1446, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d1446, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1446, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d4395, d1446, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13748 (p : Pattern) (guard : d4395 p = 1) : d1447 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1447, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13747 p hg
    simpa only [d1447, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1447, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7929 p hg
    simpa only [d1447, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13749 (p : Pattern) (guard : d4395 p = 1) : d1448 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1448, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13746 p hg
    simpa only [d1448, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1448, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13748 p hg
    simpa only [d1448, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13750 (p : Pattern) (guard : d4395 p = 1) : d1449 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1449, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d1449, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1449, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13749 p hg
    simpa only [d1449, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13751 (p : Pattern) (guard : d4395 p = 1) : d1450 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1450, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1450, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1450, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4395, d1450, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13752 (p : Pattern) (guard : d4395 p = 1) : d1451 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d1451, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13751 p hg
    simpa only [d1451, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13753 (p : Pattern) (guard : d4395 p = 1) : d1452 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13752 p hg
    simpa only [d1452, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1452, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13754 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d4395, d1453, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13755 (p : Pattern) (guard : d4395 p = 1) : d1454 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1454, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13754 p hg
    simpa only [d1454, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1454, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1454, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13756 (p : Pattern) (guard : d4395 p = 1) : d1455 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1455, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13755 p hg
    simpa only [d1455, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1455, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d1455, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13757 (p : Pattern) (guard : d4395 p = 1) : d1456 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13753 p hg
    simpa only [d1456, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13756 p hg
    simpa only [d1456, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13758 (p : Pattern) (guard : d4395 p = 1) : d1457 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1457, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13750 p hg
    simpa only [d1457, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1457, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13757 p hg
    simpa only [d1457, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13759 (p : Pattern) (guard : d4395 p = 1) : d1451 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1451, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13751 p hg
    simpa only [d1451, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13760 (p : Pattern) (guard : d4395 p = 1) : d1452 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13759 p hg
    simpa only [d1452, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1452, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13761 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d1073 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d4395, d1453, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13762 (p : Pattern) (guard : d4395 p = 1) : d1454 p ≤ (0 : Int) + d1074 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1454, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13761 p hg
    simpa only [d1454, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1454, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1454, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13763 (p : Pattern) (guard : d4395 p = 1) : d1455 p ≤ (0 : Int) + d1075 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1455, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d1455, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1455, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d1455, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13764 (p : Pattern) (guard : d4395 p = 1) : d1456 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13760 p hg
    simpa only [d1456, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1456, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13765 (p : Pattern) (guard : d4395 p = 1) : d1458 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1458, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d1458, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1458, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d1458, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13766 (p : Pattern) (guard : d4395 p = 1) : d1459 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1459, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13758 p hg
    simpa only [d1459, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1459, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d1459, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13767 (p : Pattern) (guard : d4395 p = 1) : d1439 p ≤ (0 : Int) + d1080 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1439, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d4395, d1439, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1439, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4395, d1439, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13768 (p : Pattern) (guard : d4395 p = 1) : d1440 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1440, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d1440, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1440, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d1440, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13769 (p : Pattern) (guard : d4395 p = 1) : d1441 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1441, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1441, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1441, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d4395, d1441, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13770 (p : Pattern) (guard : d4395 p = 1) : d1442 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1442, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d1442, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1442, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13742 p hg
    simpa only [d1442, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13771 (p : Pattern) (guard : d4395 p = 1) : d1443 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1443, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13768 p hg
    simpa only [d1443, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1443, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13770 p hg
    simpa only [d1443, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13772 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d1085 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d4395, d1453, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13773 (p : Pattern) (guard : d4395 p = 1) : d1460 p ≤ (0 : Int) + d1086 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1460, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13772 p hg
    simpa only [d1460, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1460, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1460, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13774 (p : Pattern) (guard : d4395 p = 1) : d1461 p ≤ (0 : Int) + d1087 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1461, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13773 p hg
    simpa only [d1461, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1461, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13748 p hg
    simpa only [d1461, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13775 (p : Pattern) (guard : d4395 p = 1) : d1462 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1462, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13771 p hg
    simpa only [d1462, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1462, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13774 p hg
    simpa only [d1462, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13776 (p : Pattern) (guard : d4395 p = 1) : d1451 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6583 p hg
    simpa only [d1451, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1451, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13751 p hg
    simpa only [d1451, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13777 (p : Pattern) (guard : d4395 p = 1) : d1452 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13776 p hg
    simpa only [d1452, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1452, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1452, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13778 (p : Pattern) (guard : d4395 p = 1) : d1456 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13777 p hg
    simpa only [d1456, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13756 p hg
    simpa only [d1456, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13779 (p : Pattern) (guard : d4395 p = 1) : d1463 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1463, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d1463, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1463, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13778 p hg
    simpa only [d1463, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13780 (p : Pattern) (guard : d4395 p = 1) : d1464 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1464, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13778 p hg
    simpa only [d1464, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1464, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1464, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13781 (p : Pattern) (guard : d4395 p = 1) : d1465 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1465, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d1465, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1465, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13780 p hg
    simpa only [d1465, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13782 (p : Pattern) (guard : d4395 p = 1) : d1466 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1466, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13766 p hg
    simpa only [d1466, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1466, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13781 p hg
    simpa only [d1466, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13783 (p : Pattern) (guard : d4395 p = 1) : d1467 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1467, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13713 p hg
    simpa only [d1467, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1467, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13782 p hg
    simpa only [d1467, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13784 (p : Pattern) (guard : d4395 p = 1) : d1468 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1468, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13738 p hg
    simpa only [d1468, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1468, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13783 p hg
    simpa only [d1468, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13785 (p : Pattern) (guard : d4395 p = 1) : d1469 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1469, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d1469, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1469, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4395, d1469, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13786 (p : Pattern) (guard : d4395 p = 1) : d1470 p ≤ (0 : Int) + d1099 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1470, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13785 p hg
    simpa only [d1470, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1470, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d1470, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13787 (p : Pattern) (guard : d4395 p = 1) : d1471 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1471, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13786 p hg
    simpa only [d1471, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1471, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7986 p hg
    simpa only [d1471, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13788 (p : Pattern) (guard : d4395 p = 1) : d1472 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1472, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13702 p hg
    simpa only [d1472, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1472, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13787 p hg
    simpa only [d1472, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13789 (p : Pattern) (guard : d4395 p = 1) : d1473 p ≤ (0 : Int) + d1104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1473, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13733 p hg
    simpa only [d1473, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1473, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13788 p hg
    simpa only [d1473, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13790 (p : Pattern) (guard : d4395 p = 1) : d1474 p ≤ (0 : Int) + d1105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1474, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13788 p hg
    simpa only [d1474, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1474, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1474, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13791 (p : Pattern) (guard : d4395 p = 1) : d1475 p ≤ (0 : Int) + d1106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1475, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13789 p hg
    simpa only [d1475, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1475, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13790 p hg
    simpa only [d1475, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13792 (p : Pattern) (guard : d4395 p = 1) : d1476 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1476, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d1476, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1476, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13791 p hg
    simpa only [d1476, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13793 (p : Pattern) (guard : d4395 p = 1) : d1477 p ≤ (0 : Int) + d1108 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1477, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13713 p hg
    simpa only [d1477, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1477, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13792 p hg
    simpa only [d1477, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13794 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d1109 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10295 p hg
    simpa only [d4395, d1453, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13795 (p : Pattern) (guard : d4395 p = 1) : d1460 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1460, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13794 p hg
    simpa only [d1460, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1460, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1460, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13796 (p : Pattern) (guard : d4395 p = 1) : d1461 p ≤ (0 : Int) + d1111 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1461, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13795 p hg
    simpa only [d1461, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1461, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13748 p hg
    simpa only [d1461, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13797 (p : Pattern) (guard : d4395 p = 1) : d1462 p ≤ (0 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1462, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d1462, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1462, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d1462, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13798 (p : Pattern) (guard : d4395 p = 1) : d1463 p ≤ (0 : Int) + d1113 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1463, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13797 p hg
    simpa only [d1463, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1463, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13757 p hg
    simpa only [d1463, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13799 (p : Pattern) (guard : d4395 p = 1) : d1456 p ≤ (0 : Int) + d1114 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13760 p hg
    simpa only [d1456, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1456, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13756 p hg
    simpa only [d1456, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13800 (p : Pattern) (guard : d4395 p = 1) : d1458 p ≤ (0 : Int) + d1115 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1458, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13799 p hg
    simpa only [d1458, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1458, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d1458, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13801 (p : Pattern) (guard : d4395 p = 1) : d1478 p ≤ (0 : Int) + d1116 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1478, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13798 p hg
    simpa only [d1478, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1478, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13800 p hg
    simpa only [d1478, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13802 (p : Pattern) (guard : d4395 p = 1) : d1479 p ≤ (0 : Int) + d1118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1479, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8005 p hg
    simpa only [d4395, d1479, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1479, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4395, d1479, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13803 (p : Pattern) (guard : d4395 p = 1) : d1480 p ≤ (0 : Int) + d1119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1480, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d1480, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1480, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13802 p hg
    simpa only [d1480, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13804 (p : Pattern) (guard : d4395 p = 1) : d1481 p ≤ (0 : Int) + d1120 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1481, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d1481, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1481, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d4395, d1481, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13805 (p : Pattern) (guard : d4395 p = 1) : d279 p ≤ (0 : Int) + d1121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d4395, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4395, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13806 (p : Pattern) (guard : d4395 p = 1) : d1482 p ≤ (0 : Int) + d1122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1482, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13804 p hg
    simpa only [d1482, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1482, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13805 p hg
    simpa only [d1482, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13807 (p : Pattern) (guard : d4395 p = 1) : d1483 p ≤ (0 : Int) + d1123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1483, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13803 p hg
    simpa only [d1483, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1483, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13806 p hg
    simpa only [d1483, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13808 (p : Pattern) (guard : d4395 p = 1) : d1484 p ≤ (0 : Int) + d1125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1484, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13754 p hg
    simpa only [d1484, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1484, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d1484, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13809 (p : Pattern) (guard : d4395 p = 1) : d1485 p ≤ (0 : Int) + d1124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1485, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d1485, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1485, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d4395, d1485, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13810 (p : Pattern) (guard : d4395 p = 1) : d1486 p ≤ (0 : Int) + d1130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1486, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13809 p hg
    simpa only [d1486, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1486, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8019 p hg
    simpa only [d1486, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13811 (p : Pattern) (guard : d4395 p = 1) : d1487 p ≤ (0 : Int) + d1131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1487, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13808 p hg
    simpa only [d1487, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1487, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13810 p hg
    simpa only [d1487, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13812 (p : Pattern) (guard : d4395 p = 1) : d1488 p ≤ (0 : Int) + d1132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1488, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13807 p hg
    simpa only [d1488, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1488, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13811 p hg
    simpa only [d1488, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13813 (p : Pattern) (guard : d4395 p = 1) : d1489 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1489, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1489, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1489, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d4395, d1489, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13814 (p : Pattern) (guard : d4395 p = 1) : d1490 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1490, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8025 p hg
    simpa only [d4395, d1490, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1490, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4395, d1490, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13815 (p : Pattern) (guard : d4395 p = 1) : d1491 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1491, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13813 p hg
    simpa only [d1491, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1491, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13814 p hg
    simpa only [d1491, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13816 (p : Pattern) (guard : d4395 p = 1) : d1492 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1492, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13815 p hg
    simpa only [d1492, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1492, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1492, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13817 (p : Pattern) (guard : d4395 p = 1) : d1493 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1493, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1493, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1493, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10327 p hg
    simpa only [d4395, d1493, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13818 (p : Pattern) (guard : d4395 p = 1) : d1494 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1494, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13817 p hg
    simpa only [d1494, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1494, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8031 p hg
    simpa only [d1494, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13819 (p : Pattern) (guard : d4395 p = 1) : d1495 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1495, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13818 p hg
    simpa only [d1495, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1495, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1495, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13820 (p : Pattern) (guard : d4395 p = 1) : d1496 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1496, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13816 p hg
    simpa only [d1496, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1496, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13819 p hg
    simpa only [d1496, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13821 (p : Pattern) (guard : d4395 p = 1) : d1497 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1497, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13812 p hg
    simpa only [d1497, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1497, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13820 p hg
    simpa only [d1497, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13822 (p : Pattern) (guard : d4395 p = 1) : d1498 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1498, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13820 p hg
    simpa only [d1498, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1498, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1498, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13823 (p : Pattern) (guard : d4395 p = 1) : d1499 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1499, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13821 p hg
    simpa only [d1499, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1499, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13822 p hg
    simpa only [d1499, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13824 (p : Pattern) (guard : d4395 p = 1) : d1500 p ≤ (0 : Int) + d1147 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1500, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13801 p hg
    simpa only [d1500, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1500, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13823 p hg
    simpa only [d1500, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13825 (p : Pattern) (guard : d4395 p = 1) : d1501 p ≤ (0 : Int) + d1148 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1501, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13713 p hg
    simpa only [d1501, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1501, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13824 p hg
    simpa only [d1501, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13826 (p : Pattern) (guard : d4395 p = 1) : d1502 p ≤ (0 : Int) + d1149 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1502, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13793 p hg
    simpa only [d1502, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1502, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13825 p hg
    simpa only [d1502, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13827 (p : Pattern) (guard : d4395 p = 1) : d1503 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1503, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13784 p hg
    simpa only [d1503, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1503, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13826 p hg
    simpa only [d1503, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13828 (p : Pattern) (guard : d1 p = 1) : d1503 p ≤ (1 : Int) + d1503 p := by
  omega
theorem compare13829 (p : Pattern) (guard : d0 p = 1) : d1399 p ≤ (0 : Int) + d362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13830 (p : Pattern) (guard : d4670 p = 1) : d1400 p ≤ (0 : Int) + d790 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1400, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1400, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1400, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13829 p hg
    simpa only [d4670, d1400, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13831 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13832 (p : Pattern) (guard : d4395 p = 1) : d1401 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1401, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1401, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1401, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13831 p hg
    simpa only [d4395, d1401, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13833 (p : Pattern) (guard : d4670 p = 1) : d1402 p ≤ (0 : Int) + d792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1402, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13832 p hg
    simpa only [d4670, d1402, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1402, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13539 p hg
    simpa only [d4670, d1402, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13834 (p : Pattern) (guard : d4670 p = 1) : d1403 p ≤ (0 : Int) + d793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1403, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13830 p hg
    simpa only [d1403, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1403, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13833 p hg
    simpa only [d1403, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13835 (p : Pattern) (guard : d0 p = 1) : d1165 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13836 (p : Pattern) (guard : d4395 p = 1) : d1404 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1404, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1404, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1404, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13835 p hg
    simpa only [d4395, d1404, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13837 (p : Pattern) (guard : d0 p = 1) : d1405 p ≤ (0 : Int) + d387 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13838 (p : Pattern) (guard : d4670 p = 1) : d1406 p ≤ (0 : Int) + d794 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1406, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13836 p hg
    simpa only [d4670, d1406, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1406, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13837 p hg
    simpa only [d4670, d1406, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13839 (p : Pattern) (guard : d0 p = 1) : d1171 p ≤ (0 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13840 (p : Pattern) (guard : d4395 p = 1) : d1407 p ≤ (0 : Int) + d799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1407, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d1407, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1407, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13839 p hg
    simpa only [d4395, d1407, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13841 (p : Pattern) (guard : d4670 p = 1) : d1408 p ≤ (0 : Int) + d800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1408, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13840 p hg
    simpa only [d4670, d1408, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1408, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13603 p hg
    simpa only [d4670, d1408, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13842 (p : Pattern) (guard : d4670 p = 1) : d1409 p ≤ (0 : Int) + d801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1409, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13838 p hg
    simpa only [d1409, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1409, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d1409, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13843 (p : Pattern) (guard : d4670 p = 1) : d1410 p ≤ (0 : Int) + d802 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1410, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13834 p hg
    simpa only [d1410, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1410, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13842 p hg
    simpa only [d1410, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13844 (p : Pattern) (guard : d0 p = 1) : d1411 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13845 (p : Pattern) (guard : d4670 p = 1) : d1412 p ≤ (0 : Int) + d803 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1412, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1412, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1412, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13844 p hg
    simpa only [d4670, d1412, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13846 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13847 (p : Pattern) (guard : d4395 p = 1) : d1413 p ≤ (0 : Int) + d804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1413, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d1413, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1413, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13846 p hg
    simpa only [d4395, d1413, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13848 (p : Pattern) (guard : d4670 p = 1) : d1414 p ≤ (0 : Int) + d805 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1414, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13847 p hg
    simpa only [d4670, d1414, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1414, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1414, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13849 (p : Pattern) (guard : d4670 p = 1) : d1415 p ≤ (0 : Int) + d806 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1415, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13845 p hg
    simpa only [d1415, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1415, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d1415, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13850 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13851 (p : Pattern) (guard : d4395 p = 1) : d1416 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1416, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1416, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1416, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13850 p hg
    simpa only [d4395, d1416, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13852 (p : Pattern) (guard : d0 p = 1) : d1417 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13853 (p : Pattern) (guard : d4670 p = 1) : d1418 p ≤ (0 : Int) + d807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1418, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13851 p hg
    simpa only [d4670, d1418, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1418, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d4670, d1418, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13854 (p : Pattern) (guard : d4670 p = 1) : d1419 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1419, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13853 p hg
    simpa only [d1419, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1419, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d1419, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13855 (p : Pattern) (guard : d4670 p = 1) : d1420 p ≤ (0 : Int) + d813 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1420, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13849 p hg
    simpa only [d1420, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1420, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13854 p hg
    simpa only [d1420, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13856 (p : Pattern) (guard : d4670 p = 1) : d1421 p ≤ (0 : Int) + d814 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1421, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13843 p hg
    simpa only [d1421, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1421, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13855 p hg
    simpa only [d1421, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13857 (p : Pattern) (guard : d0 p = 1) : d1411 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13858 (p : Pattern) (guard : d4670 p = 1) : d1412 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1412, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1412, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1412, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13857 p hg
    simpa only [d4670, d1412, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13859 (p : Pattern) (guard : d4670 p = 1) : d1415 p ≤ (0 : Int) + d816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1415, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13858 p hg
    simpa only [d1415, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1415, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d1415, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
