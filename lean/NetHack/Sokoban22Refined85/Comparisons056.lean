/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7840 (p : Pattern) (guard : d4395 p = 1) : d93 p ≤ (0 : Int) + d93 p := by
  omega
theorem compare7841 (p : Pattern) (guard : d4395 p = 1) : d987 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7839 p hg
    simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7840 p hg
    simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7842 (p : Pattern) (guard : d4395 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare7843 (p : Pattern) (guard : d4395 p = 1) : d988 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d988, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7841 p hg
    simpa only [d988, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d988, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d988, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7844 (p : Pattern) (guard : d4395 p = 1) : d989 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d989, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7836 p hg
    simpa only [d989, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d989, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7843 p hg
    simpa only [d989, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7845 (p : Pattern) (guard : d4395 p = 1) : d990 p ≤ (0 : Int) + d1423 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d990, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7827 p hg
    simpa only [d990, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d990, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7844 p hg
    simpa only [d990, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7846 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7847 (p : Pattern) (guard : d4395 p = 1) : d991 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7846 p hg
    simpa only [d4395, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7848 (p : Pattern) (guard : d4395 p = 1) : d992 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d992, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d992, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d992, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4395, d992, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7849 (p : Pattern) (guard : d4395 p = 1) : d993 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d993, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7847 p hg
    simpa only [d993, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d993, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7848 p hg
    simpa only [d993, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7850 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7851 (p : Pattern) (guard : d4395 p = 1) : d994 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d994, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d994, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d994, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7850 p hg
    simpa only [d4395, d994, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7852 (p : Pattern) (guard : d4395 p = 1) : d995 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d995, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7851 p hg
    simpa only [d995, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d995, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7794 p hg
    simpa only [d995, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7853 (p : Pattern) (guard : d4395 p = 1) : d996 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d996, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7849 p hg
    simpa only [d996, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d996, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d996, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7854 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7855 (p : Pattern) (guard : d4395 p = 1) : d997 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d997, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d997, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d997, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7854 p hg
    simpa only [d4395, d997, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7856 (p : Pattern) (guard : d4395 p = 1) : d960 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d960, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d960, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d960, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4395, d960, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7857 (p : Pattern) (guard : d4395 p = 1) : d998 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d998, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7855 p hg
    simpa only [d998, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d998, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7856 p hg
    simpa only [d998, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7858 (p : Pattern) (guard : d4395 p = 1) : d999 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d999, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7857 p hg
    simpa only [d999, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d999, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d999, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7859 (p : Pattern) (guard : d4395 p = 1) : d1000 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1000, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7853 p hg
    simpa only [d1000, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1000, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7858 p hg
    simpa only [d1000, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7860 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7861 (p : Pattern) (guard : d4395 p = 1) : d1001 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7860 p hg
    simpa only [d4395, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7862 (p : Pattern) (guard : d4395 p = 1) : d1002 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1002, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7861 p hg
    simpa only [d1002, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1002, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d1002, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7863 (p : Pattern) (guard : d4395 p = 1) : d1003 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1003, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7862 p hg
    simpa only [d1003, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1003, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d1003, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7864 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7865 (p : Pattern) (guard : d4395 p = 1) : d966 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d966, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d966, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d966, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d4395, d966, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7866 (p : Pattern) (guard : d4395 p = 1) : d1004 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1004, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7865 p hg
    simpa only [d1004, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1004, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d1004, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7867 (p : Pattern) (guard : d4395 p = 1) : d1005 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1005, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7866 p hg
    simpa only [d1005, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1005, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d1005, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7868 (p : Pattern) (guard : d4395 p = 1) : d1006 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1006, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d1006, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1006, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7867 p hg
    simpa only [d1006, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7869 (p : Pattern) (guard : d4395 p = 1) : d1007 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1007, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7859 p hg
    simpa only [d1007, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1007, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7868 p hg
    simpa only [d1007, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7870 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7871 (p : Pattern) (guard : d4395 p = 1) : d1008 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7870 p hg
    simpa only [d4395, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7872 (p : Pattern) (guard : d4395 p = 1) : d1009 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1009, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7871 p hg
    simpa only [d1009, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1009, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d1009, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7873 (p : Pattern) (guard : d4395 p = 1) : d1010 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1010, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7872 p hg
    simpa only [d1010, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1010, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d1010, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7874 (p : Pattern) (guard : d4395 p = 1) : d1011 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1011, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7873 p hg
    simpa only [d1011, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1011, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7867 p hg
    simpa only [d1011, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7875 (p : Pattern) (guard : d4395 p = 1) : d1012 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1012, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7874 p hg
    simpa only [d1012, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1012, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1012, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7876 (p : Pattern) (guard : d4395 p = 1) : d1013 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1013, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7869 p hg
    simpa only [d1013, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1013, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7875 p hg
    simpa only [d1013, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7877 (p : Pattern) (guard : d4395 p = 1) : d1014 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1014, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7845 p hg
    simpa only [d1014, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1014, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7876 p hg
    simpa only [d1014, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7878 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7879 (p : Pattern) (guard : d4395 p = 1) : d1015 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7878 p hg
    simpa only [d4395, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7880 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7881 (p : Pattern) (guard : d4395 p = 1) : d1016 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1016, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d1016, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1016, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7880 p hg
    simpa only [d4395, d1016, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7882 (p : Pattern) (guard : d4395 p = 1) : d1017 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1017, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7879 p hg
    simpa only [d1017, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1017, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7881 p hg
    simpa only [d1017, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7883 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7884 (p : Pattern) (guard : d4395 p = 1) : d1018 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1018, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1018, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1018, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d4395, d1018, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7885 (p : Pattern) (guard : d4395 p = 1) : d1019 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1019, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7884 p hg
    simpa only [d1019, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1019, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7794 p hg
    simpa only [d1019, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7886 (p : Pattern) (guard : d4395 p = 1) : d1020 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1020, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7882 p hg
    simpa only [d1020, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1020, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7885 p hg
    simpa only [d1020, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7887 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d1167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7888 (p : Pattern) (guard : d4395 p = 1) : d1021 p ≤ (0 : Int) + d1431 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1021, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1021, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1021, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7887 p hg
    simpa only [d4395, d1021, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7889 (p : Pattern) (guard : d4395 p = 1) : d1022 p ≤ (0 : Int) + d1432 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1022, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d1022, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1022, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7856 p hg
    simpa only [d1022, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7890 (p : Pattern) (guard : d4395 p = 1) : d1023 p ≤ (0 : Int) + d1433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1023, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7889 p hg
    simpa only [d1023, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1023, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d1023, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7891 (p : Pattern) (guard : d4395 p = 1) : d1024 p ≤ (0 : Int) + d1434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1024, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d1024, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1024, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7890 p hg
    simpa only [d1024, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7892 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7893 (p : Pattern) (guard : d4395 p = 1) : d1025 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d4395, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7894 (p : Pattern) (guard : d4395 p = 1) : d1026 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1026, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7893 p hg
    simpa only [d1026, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1026, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d1026, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7895 (p : Pattern) (guard : d4395 p = 1) : d1027 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1027, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7894 p hg
    simpa only [d1027, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1027, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d1027, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7896 (p : Pattern) (guard : d4395 p = 1) : d1028 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1028, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d1028, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1028, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7867 p hg
    simpa only [d1028, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7897 (p : Pattern) (guard : d4395 p = 1) : d1029 p ≤ (0 : Int) + d1435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1029, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7891 p hg
    simpa only [d1029, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1029, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7896 p hg
    simpa only [d1029, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7898 (p : Pattern) (guard : d4395 p = 1) : d1030 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1030, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7826 p hg
    simpa only [d1030, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1030, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7843 p hg
    simpa only [d1030, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7899 (p : Pattern) (guard : d4395 p = 1) : d1031 p ≤ (0 : Int) + d1436 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1031, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7897 p hg
    simpa only [d1031, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1031, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d1031, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7900 (p : Pattern) (guard : d4395 p = 1) : d1032 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1032, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d1032, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1032, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7848 p hg
    simpa only [d1032, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7901 (p : Pattern) (guard : d4395 p = 1) : d1033 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1033, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d1033, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1033, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d1033, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7902 (p : Pattern) (guard : d4395 p = 1) : d1034 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1034, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7833 p hg
    simpa only [d1034, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1034, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7856 p hg
    simpa only [d1034, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7903 (p : Pattern) (guard : d4395 p = 1) : d1035 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1035, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7902 p hg
    simpa only [d1035, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1035, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d1035, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7904 (p : Pattern) (guard : d4395 p = 1) : d1036 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1036, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7901 p hg
    simpa only [d1036, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1036, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7903 p hg
    simpa only [d1036, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7905 (p : Pattern) (guard : d4395 p = 1) : d1037 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1037, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d1037, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1037, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7868 p hg
    simpa only [d1037, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7906 (p : Pattern) (guard : d4395 p = 1) : d1038 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1038, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7868 p hg
    simpa only [d1038, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1038, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1038, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7907 (p : Pattern) (guard : d4395 p = 1) : d1039 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1039, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7905 p hg
    simpa only [d1039, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1039, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7906 p hg
    simpa only [d1039, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7908 (p : Pattern) (guard : d4395 p = 1) : d1040 p ≤ (0 : Int) + d1437 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1040, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7899 p hg
    simpa only [d1040, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1040, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7907 p hg
    simpa only [d1040, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7909 (p : Pattern) (guard : d4395 p = 1) : d1041 p ≤ (0 : Int) + d1438 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1041, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d1041, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1041, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7908 p hg
    simpa only [d1041, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7910 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7911 (p : Pattern) (guard : d4395 p = 1) : d1042 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7910 p hg
    simpa only [d4395, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7912 (p : Pattern) (guard : d1 p = 1) : d1043 p ≤ (0 : Int) + d1043 p := by
  omega
theorem compare7913 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7914 (p : Pattern) (guard : d4395 p = 1) : d1044 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1044, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d4395, d1044, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1044, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d4395, d1044, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7915 (p : Pattern) (guard : d4395 p = 1) : d1045 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1045, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7911 p hg
    simpa only [d1045, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1045, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7914 p hg
    simpa only [d1045, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7916 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7917 (p : Pattern) (guard : d4395 p = 1) : d1046 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1046, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1046, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1046, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7916 p hg
    simpa only [d4395, d1046, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7918 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
theorem compare7919 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7920 (p : Pattern) (guard : d4395 p = 1) : d1047 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d4395, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d4395, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7921 (p : Pattern) (guard : d4395 p = 1) : d1048 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1048, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7917 p hg
    simpa only [d1048, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1048, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7920 p hg
    simpa only [d1048, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7922 (p : Pattern) (guard : d4395 p = 1) : d1049 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1049, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7915 p hg
    simpa only [d1049, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1049, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7921 p hg
    simpa only [d1049, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7923 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d1284 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7924 (p : Pattern) (guard : d4395 p = 1) : d1050 p ≤ (0 : Int) + d1444 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1050, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1050, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1050, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d4395, d1050, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7925 (p : Pattern) (guard : d4395 p = 1) : d1051 p ≤ (0 : Int) + d1051 p := by
  omega
theorem compare7926 (p : Pattern) (guard : d4395 p = 1) : d1052 p ≤ (0 : Int) + d1445 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1052, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7924 p hg
    simpa only [d1052, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1052, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1052, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7927 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7928 (p : Pattern) (guard : d4395 p = 1) : d1051 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1051, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d1051, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1051, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7927 p hg
    simpa only [d4395, d1051, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7929 (p : Pattern) (guard : d4395 p = 1) : d1054 p ≤ (0 : Int) + d1054 p := by
  omega
theorem compare7930 (p : Pattern) (guard : d4395 p = 1) : d1055 p ≤ (0 : Int) + d1447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1055, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7928 p hg
    simpa only [d1055, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1055, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7929 p hg
    simpa only [d1055, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7931 (p : Pattern) (guard : d4395 p = 1) : d1056 p ≤ (0 : Int) + d1448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1056, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7926 p hg
    simpa only [d1056, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1056, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7930 p hg
    simpa only [d1056, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7932 (p : Pattern) (guard : d4395 p = 1) : d1057 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1057, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7922 p hg
    simpa only [d1057, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1057, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7931 p hg
    simpa only [d1057, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7933 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7934 (p : Pattern) (guard : d4395 p = 1) : d1058 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d4395, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7935 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7936 (p : Pattern) (guard : d4395 p = 1) : d1059 p ≤ (0 : Int) + d1450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1059, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1059, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1059, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4395, d1059, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7937 (p : Pattern) (guard : d4395 p = 1) : d1060 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1060, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1060, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1060, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1060, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7938 (p : Pattern) (guard : d4395 p = 1) : d1062 p ≤ (0 : Int) + d1062 p := by
  omega
theorem compare7939 (p : Pattern) (guard : d4395 p = 1) : d1063 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1063, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d1063, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1063, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1063, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7940 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7941 (p : Pattern) (guard : d4395 p = 1) : d1059 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1059, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1059, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1059, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d4395, d1059, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7942 (p : Pattern) (guard : d4395 p = 1) : d1064 p ≤ (0 : Int) + d1064 p := by
  omega
theorem compare7943 (p : Pattern) (guard : d4395 p = 1) : d1065 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1065, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d1065, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1065, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1065, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7944 (p : Pattern) (guard : d4395 p = 1) : d1066 p ≤ (0 : Int) + d1066 p := by
  omega
theorem compare7945 (p : Pattern) (guard : d4395 p = 1) : d1067 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1067, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7943 p hg
    simpa only [d1067, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1067, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d1067, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7946 (p : Pattern) (guard : d4395 p = 1) : d1068 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1068, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7939 p hg
    simpa only [d1068, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1068, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d1068, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7947 (p : Pattern) (guard : d4395 p = 1) : d1069 p ≤ (0 : Int) + d1457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1069, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7932 p hg
    simpa only [d1069, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1069, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7946 p hg
    simpa only [d1069, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7948 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7949 (p : Pattern) (guard : d4395 p = 1) : d1070 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7948 p hg
    simpa only [d4395, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7950 (p : Pattern) (guard : d4395 p = 1) : d1071 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1071, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7949 p hg
    simpa only [d1071, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1071, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1071, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7951 (p : Pattern) (guard : d4395 p = 1) : d1072 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1072, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1072, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1072, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1072, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7952 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7953 (p : Pattern) (guard : d4395 p = 1) : d1073 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1073, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1073, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1073, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d4395, d1073, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7954 (p : Pattern) (guard : d4395 p = 1) : d1074 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1074, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7953 p hg
    simpa only [d1074, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1074, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1074, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7955 (p : Pattern) (guard : d4395 p = 1) : d1075 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1075, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1075, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1075, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d1075, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7956 (p : Pattern) (guard : d4395 p = 1) : d1076 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1076, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d1076, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1076, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7955 p hg
    simpa only [d1076, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7957 (p : Pattern) (guard : d4395 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare7958 (p : Pattern) (guard : d4395 p = 1) : d1077 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1077, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1077, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1077, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d1077, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7959 (p : Pattern) (guard : d4395 p = 1) : d1078 p ≤ (0 : Int) + d1459 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1078, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7947 p hg
    simpa only [d1078, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1078, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7958 p hg
    simpa only [d1078, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7960 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7961 (p : Pattern) (guard : d4395 p = 1) : d1079 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7960 p hg
    simpa only [d4395, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7962 (p : Pattern) (guard : d4395 p = 1) : d1080 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1080, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d4395, d1080, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1080, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4395, d1080, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7963 (p : Pattern) (guard : d4395 p = 1) : d1081 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1081, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d1081, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1081, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7962 p hg
    simpa only [d1081, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7964 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7965 (p : Pattern) (guard : d4395 p = 1) : d1082 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1082, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1082, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1082, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7964 p hg
    simpa only [d4395, d1082, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7966 (p : Pattern) (guard : d4395 p = 1) : d1083 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1083, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7965 p hg
    simpa only [d1083, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1083, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7920 p hg
    simpa only [d1083, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7967 (p : Pattern) (guard : d4395 p = 1) : d1084 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1084, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7963 p hg
    simpa only [d1084, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1084, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7966 p hg
    simpa only [d1084, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7968 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7969 (p : Pattern) (guard : d4395 p = 1) : d1085 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1085, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1085, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1085, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7968 p hg
    simpa only [d4395, d1085, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7970 (p : Pattern) (guard : d4395 p = 1) : d1086 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1086, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7969 p hg
    simpa only [d1086, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1086, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1086, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7971 (p : Pattern) (guard : d4395 p = 1) : d1087 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1087, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7970 p hg
    simpa only [d1087, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1087, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7930 p hg
    simpa only [d1087, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7972 (p : Pattern) (guard : d4395 p = 1) : d1088 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1088, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1088, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1088, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1088, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7973 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7974 (p : Pattern) (guard : d4395 p = 1) : d1089 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7973 p hg
    simpa only [d4395, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7975 (p : Pattern) (guard : d4395 p = 1) : d1090 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1090, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7974 p hg
    simpa only [d1090, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1090, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1090, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7976 (p : Pattern) (guard : d4395 p = 1) : d1091 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1091, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d1091, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1091, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1091, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7977 (p : Pattern) (guard : d4395 p = 1) : d1092 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1092, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7976 p hg
    simpa only [d1092, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1092, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d1092, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7978 (p : Pattern) (guard : d4395 p = 1) : d1093 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1093, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7972 p hg
    simpa only [d1093, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1093, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d1093, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7979 (p : Pattern) (guard : d4395 p = 1) : d1094 p ≤ (0 : Int) + d1464 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1094, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d1094, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1094, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1094, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
