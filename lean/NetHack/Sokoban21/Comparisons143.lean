/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons142
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20020 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (16 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20019 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20021 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (16 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19698 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20020 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20022 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (16 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19696 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20021 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20023 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19812 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20024 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (16 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20022 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20023 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20025 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (16 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20018 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20024 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20026 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (16 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20012 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20027 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (16 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20025 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20026 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20028 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (16 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20013 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20027 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20029 (pattern : Twelve) (guard : d1872 pattern = 1) : d869 pattern ≤ (16 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19643 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20028 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20030 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (16 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19646 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20031 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (16 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19650 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20032 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (16 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20030 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20031 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20033 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (16 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20032 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20034 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19662 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20035 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20034 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19666 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20036 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (16 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20035 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20037 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (16 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20033 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20036 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20038 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (16 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19646 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20019 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20039 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (16 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20038 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20008 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20040 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (16 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19671 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20039 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20041 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (16 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19789 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20035 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20042 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (16 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20040 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20041 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20043 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (16 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20037 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20042 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20044 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (16 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19650 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19697 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20045 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (16 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20038 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20044 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20046 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (16 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20045 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20047 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (16 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20048 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (16 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20047 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20049 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (16 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20048 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20035 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20050 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (16 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20046 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20049 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20051 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (16 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19674 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20052 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (16 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19988 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19540 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20053 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (16 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20052 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20054 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (16 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20051 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20053 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20055 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (16 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19696 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20054 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20056 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (16 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19852 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20057 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (16 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20056 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19815 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20058 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19666 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20059 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (16 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20057 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20058 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20060 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (16 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20055 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20059 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20061 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (16 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20050 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20060 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20062 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (16 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20042 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20063 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (16 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20061 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20062 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20064 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (16 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20043 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20063 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20065 (pattern : Twelve) (guard : d1872 pattern = 1) : d906 pattern ≤ (16 : Int) + d1353 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19714 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20064 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20066 (pattern : Twelve) (guard : d1872 pattern = 1) : d907 pattern ≤ (16 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20029 pattern childGuard
    simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20065 pattern childGuard
    simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20067 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (16 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19469 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20068 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (16 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19784 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20067 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20069 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19799 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19471 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20070 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20069 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20071 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (16 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19795 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20070 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20072 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (16 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20068 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20071 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20073 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (16 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19799 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20074 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (16 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19808 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20073 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20075 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19818 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19953 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20076 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (16 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20075 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20077 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (16 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19817 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20076 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20078 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (16 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20074 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20077 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20079 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (16 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20071 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20080 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (16 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20078 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20079 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20081 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20072 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20080 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20082 (pattern : Twelve) (guard : d1872 pattern = 1) : d1321 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19777 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20081 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20083 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19468 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19796 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20084 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19779 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20083 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20085 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20083 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20086 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20084 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20085 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20087 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (16 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20086 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20088 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (16 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20087 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20067 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20089 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19779 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20090 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (16 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20089 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19793 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20091 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (16 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19789 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20090 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20092 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (16 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20091 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20070 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20093 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (16 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20088 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20092 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20094 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (16 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19813 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20095 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (16 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20089 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20094 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20096 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (16 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20095 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20097 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19469 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20098 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19799 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20097 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20099 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20098 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20100 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (16 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20096 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20099 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20101 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (16 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19791 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20102 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (16 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19813 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20103 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (16 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20101 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20102 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20104 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (16 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19812 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20103 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20105 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20106 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (16 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20105 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19891 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20107 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (16 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20106 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20108 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (16 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20104 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20107 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20109 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (16 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20100 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20108 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20110 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (16 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20092 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20111 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (16 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20109 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20110 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20112 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (16 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20093 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20111 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20113 (pattern : Twelve) (guard : d1872 pattern = 1) : d1353 pattern ≤ (16 : Int) + d1677 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19827 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20112 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20114 (pattern : Twelve) (guard : d1872 pattern = 1) : d1354 pattern ≤ (16 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1354, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20082 pattern childGuard
    simpa only [d1354, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1354, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20113 pattern childGuard
    simpa only [d1354, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20115 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19662 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19879 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20116 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20115 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19875 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20117 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20116 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19885 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20118 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19873 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20119 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19879 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20118 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20120 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19665 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20119 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20121 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20120 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19884 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20122 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19891 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19908 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20123 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19883 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20122 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20124 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19768 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20125 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20123 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20124 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20126 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20121 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20125 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20127 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20126 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19897 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20128 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20117 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20127 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20129 (pattern : Twelve) (guard : d1872 pattern = 1) : d1677 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19901 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20128 pattern childGuard
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20130 (pattern : Twelve) (guard : d1872 pattern = 1) : d1678 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19900 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20129 pattern childGuard
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20131 (pattern : Twelve) (guard : d0 pattern = 1) : d116 pattern ≤ (16 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20132 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (16 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20133 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (16 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20132 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20134 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (16 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19448 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20133 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20135 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (16 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20136 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (16 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20135 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20137 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (16 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19483 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20136 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20138 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (16 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20139 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (16 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20138 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20140 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (16 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20139 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20141 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (16 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20137 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20140 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20142 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (16 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20134 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20141 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20143 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (16 : Int) + d45 pattern := by
  omega
theorem c20144 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (16 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20143 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20145 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (16 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19503 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20144 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20146 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (16 : Int) + d39 pattern := by
  omega
theorem c20147 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (16 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20146 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20148 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (16 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20147 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20149 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (16 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20145 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20148 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20150 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (16 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20134 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20149 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20151 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (16 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20142 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20150 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20152 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (16 : Int) + d46 pattern := by
  omega
theorem c20153 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (16 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20152 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20154 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (16 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19475 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20153 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20155 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d38 pattern := by
  omega
theorem c20156 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (16 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20155 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20157 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (16 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20156 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20158 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (16 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20154 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20157 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20159 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (16 : Int) + d47 pattern := by
  omega
end NetHack.Sokoban21.Diagram
