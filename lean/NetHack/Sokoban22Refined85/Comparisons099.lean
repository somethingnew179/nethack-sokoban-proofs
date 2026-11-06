/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13860 (p : Pattern) (guard : d0 p = 1) : d1417 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13861 (p : Pattern) (guard : d4670 p = 1) : d1418 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1418, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13851 p hg
    simpa only [d4670, d1418, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1418, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13860 p hg
    simpa only [d4670, d1418, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13862 (p : Pattern) (guard : d4670 p = 1) : d1419 p ≤ (0 : Int) + d818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1419, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13861 p hg
    simpa only [d1419, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1419, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d1419, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13863 (p : Pattern) (guard : d4670 p = 1) : d1420 p ≤ (0 : Int) + d819 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1420, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13859 p hg
    simpa only [d1420, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1420, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13862 p hg
    simpa only [d1420, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13864 (p : Pattern) (guard : d4670 p = 1) : d92 p ≤ (0 : Int) + d820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7452 p hg
    simpa only [d4670, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d4670, d92, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13865 (p : Pattern) (guard : d4670 p = 1) : d94 p ≤ (0 : Int) + d821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d94, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13864 p hg
    simpa only [d94, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d94, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d94, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13866 (p : Pattern) (guard : d4670 p = 1) : d96 p ≤ (0 : Int) + d822 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d96, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13865 p hg
    simpa only [d96, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d96, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d96, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13867 (p : Pattern) (guard : d4670 p = 1) : d1422 p ≤ (0 : Int) + d823 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1422, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13863 p hg
    simpa only [d1422, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1422, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13866 p hg
    simpa only [d1422, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13868 (p : Pattern) (guard : d4670 p = 1) : d1423 p ≤ (0 : Int) + d824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1423, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13856 p hg
    simpa only [d1423, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1423, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13867 p hg
    simpa only [d1423, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13869 (p : Pattern) (guard : d0 p = 1) : d1399 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13870 (p : Pattern) (guard : d4670 p = 1) : d1400 p ≤ (0 : Int) + d825 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1400, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1400, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1400, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13869 p hg
    simpa only [d4670, d1400, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13871 (p : Pattern) (guard : d4670 p = 1) : d1402 p ≤ (0 : Int) + d826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1402, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13832 p hg
    simpa only [d4670, d1402, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1402, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13524 p hg
    simpa only [d4670, d1402, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13872 (p : Pattern) (guard : d4670 p = 1) : d1403 p ≤ (0 : Int) + d827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1403, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13870 p hg
    simpa only [d1403, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1403, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13871 p hg
    simpa only [d1403, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13873 (p : Pattern) (guard : d0 p = 1) : d1405 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13874 (p : Pattern) (guard : d4670 p = 1) : d1424 p ≤ (0 : Int) + d828 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1424, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13851 p hg
    simpa only [d4670, d1424, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1424, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13873 p hg
    simpa only [d4670, d1424, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13875 (p : Pattern) (guard : d4670 p = 1) : d1425 p ≤ (0 : Int) + d829 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1425, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13874 p hg
    simpa only [d1425, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1425, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d1425, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13876 (p : Pattern) (guard : d4670 p = 1) : d1426 p ≤ (0 : Int) + d830 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1426, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13872 p hg
    simpa only [d1426, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1426, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13875 p hg
    simpa only [d1426, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13877 (p : Pattern) (guard : d0 p = 1) : d1411 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13878 (p : Pattern) (guard : d4670 p = 1) : d1412 p ≤ (0 : Int) + d831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1412, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1412, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1412, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13877 p hg
    simpa only [d4670, d1412, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13879 (p : Pattern) (guard : d4670 p = 1) : d1415 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1415, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13878 p hg
    simpa only [d1415, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1415, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d1415, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13880 (p : Pattern) (guard : d4670 p = 1) : d1420 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1420, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13879 p hg
    simpa only [d1420, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1420, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13854 p hg
    simpa only [d1420, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13881 (p : Pattern) (guard : d4670 p = 1) : d1427 p ≤ (0 : Int) + d834 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1427, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13876 p hg
    simpa only [d1427, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1427, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13880 p hg
    simpa only [d1427, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13882 (p : Pattern) (guard : d4670 p = 1) : d1428 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1428, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13880 p hg
    simpa only [d1428, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1428, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1428, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13883 (p : Pattern) (guard : d4670 p = 1) : d1429 p ≤ (0 : Int) + d836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1429, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13881 p hg
    simpa only [d1429, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1429, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13882 p hg
    simpa only [d1429, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13884 (p : Pattern) (guard : d4670 p = 1) : d1430 p ≤ (0 : Int) + d837 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1430, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13868 p hg
    simpa only [d1430, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1430, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13883 p hg
    simpa only [d1430, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13885 (p : Pattern) (guard : d0 p = 1) : d1399 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13886 (p : Pattern) (guard : d4670 p = 1) : d1400 p ≤ (0 : Int) + d838 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1400, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1400, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1400, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13885 p hg
    simpa only [d4670, d1400, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13887 (p : Pattern) (guard : d4670 p = 1) : d1403 p ≤ (0 : Int) + d839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1403, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13886 p hg
    simpa only [d1403, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1403, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13871 p hg
    simpa only [d1403, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13888 (p : Pattern) (guard : d0 p = 1) : d1167 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13889 (p : Pattern) (guard : d4395 p = 1) : d1431 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1431, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1431, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1431, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13888 p hg
    simpa only [d4395, d1431, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13890 (p : Pattern) (guard : d0 p = 1) : d1405 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13891 (p : Pattern) (guard : d4670 p = 1) : d1432 p ≤ (0 : Int) + d840 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13889 p hg
    simpa only [d4670, d1432, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13890 p hg
    simpa only [d4670, d1432, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13892 (p : Pattern) (guard : d4670 p = 1) : d1433 p ≤ (0 : Int) + d841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1433, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13891 p hg
    simpa only [d1433, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1433, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d1433, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13893 (p : Pattern) (guard : d4670 p = 1) : d1434 p ≤ (0 : Int) + d842 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13887 p hg
    simpa only [d1434, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13892 p hg
    simpa only [d1434, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13894 (p : Pattern) (guard : d0 p = 1) : d1411 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13895 (p : Pattern) (guard : d4670 p = 1) : d1412 p ≤ (0 : Int) + d843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1412, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1412, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1412, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13894 p hg
    simpa only [d4670, d1412, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13896 (p : Pattern) (guard : d4670 p = 1) : d1415 p ≤ (0 : Int) + d844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1415, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13895 p hg
    simpa only [d1415, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1415, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d1415, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13897 (p : Pattern) (guard : d4670 p = 1) : d1420 p ≤ (0 : Int) + d845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1420, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13896 p hg
    simpa only [d1420, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1420, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13854 p hg
    simpa only [d1420, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13898 (p : Pattern) (guard : d4670 p = 1) : d1435 p ≤ (0 : Int) + d846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1435, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13893 p hg
    simpa only [d1435, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1435, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13897 p hg
    simpa only [d1435, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13899 (p : Pattern) (guard : d4670 p = 1) : d1422 p ≤ (0 : Int) + d847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1422, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13855 p hg
    simpa only [d1422, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1422, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13866 p hg
    simpa only [d1422, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13900 (p : Pattern) (guard : d4670 p = 1) : d1436 p ≤ (0 : Int) + d848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1436, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13898 p hg
    simpa only [d1436, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1436, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13899 p hg
    simpa only [d1436, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13901 (p : Pattern) (guard : d0 p = 1) : d1399 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13902 (p : Pattern) (guard : d4670 p = 1) : d1400 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1400, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d1400, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1400, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13901 p hg
    simpa only [d4670, d1400, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13903 (p : Pattern) (guard : d4670 p = 1) : d1403 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1403, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13902 p hg
    simpa only [d1403, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1403, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13871 p hg
    simpa only [d1403, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13904 (p : Pattern) (guard : d0 p = 1) : d1405 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13905 (p : Pattern) (guard : d4670 p = 1) : d1424 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1424, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13851 p hg
    simpa only [d4670, d1424, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1424, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13904 p hg
    simpa only [d4670, d1424, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13906 (p : Pattern) (guard : d4670 p = 1) : d1425 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1425, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13905 p hg
    simpa only [d1425, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1425, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d1425, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13907 (p : Pattern) (guard : d4670 p = 1) : d1426 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1426, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13903 p hg
    simpa only [d1426, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1426, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13906 p hg
    simpa only [d1426, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13908 (p : Pattern) (guard : d4670 p = 1) : d1427 p ≤ (0 : Int) + d852 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1427, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13907 p hg
    simpa only [d1427, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1427, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13880 p hg
    simpa only [d1427, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13909 (p : Pattern) (guard : d4670 p = 1) : d1429 p ≤ (0 : Int) + d853 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1429, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13908 p hg
    simpa only [d1429, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1429, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13882 p hg
    simpa only [d1429, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13910 (p : Pattern) (guard : d4670 p = 1) : d1437 p ≤ (0 : Int) + d854 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1437, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13900 p hg
    simpa only [d1437, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1437, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13909 p hg
    simpa only [d1437, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13911 (p : Pattern) (guard : d4670 p = 1) : d1438 p ≤ (0 : Int) + d855 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1438, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13884 p hg
    simpa only [d1438, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1438, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13910 p hg
    simpa only [d1438, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13912 (p : Pattern) (guard : d0 p = 1) : d1439 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13913 (p : Pattern) (guard : d4670 p = 1) : d1440 p ≤ (0 : Int) + d856 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1440, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1440, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1440, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13912 p hg
    simpa only [d4670, d1440, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13914 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13915 (p : Pattern) (guard : d4395 p = 1) : d1441 p ≤ (0 : Int) + d857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1441, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1441, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1441, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13914 p hg
    simpa only [d4395, d1441, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13916 (p : Pattern) (guard : d4670 p = 1) : d1442 p ≤ (0 : Int) + d858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1442, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13915 p hg
    simpa only [d4670, d1442, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1442, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13588 p hg
    simpa only [d4670, d1442, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13917 (p : Pattern) (guard : d4670 p = 1) : d1443 p ≤ (0 : Int) + d859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1443, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13913 p hg
    simpa only [d1443, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1443, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13916 p hg
    simpa only [d1443, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13918 (p : Pattern) (guard : d0 p = 1) : d1284 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13919 (p : Pattern) (guard : d4395 p = 1) : d1444 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1444, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1444, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1444, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13918 p hg
    simpa only [d4395, d1444, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13920 (p : Pattern) (guard : d4670 p = 1) : d1445 p ≤ (0 : Int) + d860 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1445, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13919 p hg
    simpa only [d4670, d1445, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1445, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d4670, d1445, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13921 (p : Pattern) (guard : d0 p = 1) : d1290 p ≤ (0 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13922 (p : Pattern) (guard : d4395 p = 1) : d1446 p ≤ (0 : Int) + d864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1446, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d1446, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1446, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13921 p hg
    simpa only [d4395, d1446, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13923 (p : Pattern) (guard : d4670 p = 1) : d1447 p ≤ (0 : Int) + d865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1447, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13922 p hg
    simpa only [d4670, d1447, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1447, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d4670, d1447, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13924 (p : Pattern) (guard : d4670 p = 1) : d1448 p ≤ (0 : Int) + d866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1448, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13920 p hg
    simpa only [d1448, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1448, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13923 p hg
    simpa only [d1448, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13925 (p : Pattern) (guard : d4670 p = 1) : d1449 p ≤ (0 : Int) + d867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1449, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13917 p hg
    simpa only [d1449, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1449, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13924 p hg
    simpa only [d1449, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13926 (p : Pattern) (guard : d0 p = 1) : d1450 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13927 (p : Pattern) (guard : d4670 p = 1) : d1451 p ≤ (0 : Int) + d868 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1451, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1451, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1451, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13926 p hg
    simpa only [d4670, d1451, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13928 (p : Pattern) (guard : d4670 p = 1) : d1452 p ≤ (0 : Int) + d871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1452, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13927 p hg
    simpa only [d1452, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1452, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1452, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13929 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13930 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13929 p hg
    simpa only [d4395, d1453, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13931 (p : Pattern) (guard : d4670 p = 1) : d1454 p ≤ (0 : Int) + d872 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1454, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13930 p hg
    simpa only [d4670, d1454, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1454, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d4670, d1454, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13932 (p : Pattern) (guard : d4670 p = 1) : d1455 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1455, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13931 p hg
    simpa only [d1455, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1455, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1455, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13933 (p : Pattern) (guard : d4670 p = 1) : d1456 p ≤ (0 : Int) + d877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1456, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13928 p hg
    simpa only [d1456, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1456, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13932 p hg
    simpa only [d1456, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13934 (p : Pattern) (guard : d4670 p = 1) : d1457 p ≤ (0 : Int) + d878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1457, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13925 p hg
    simpa only [d1457, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1457, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13933 p hg
    simpa only [d1457, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13935 (p : Pattern) (guard : d0 p = 1) : d1450 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13936 (p : Pattern) (guard : d4670 p = 1) : d1451 p ≤ (0 : Int) + d879 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1451, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1451, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1451, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13935 p hg
    simpa only [d4670, d1451, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13937 (p : Pattern) (guard : d4670 p = 1) : d1452 p ≤ (0 : Int) + d880 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1452, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13936 p hg
    simpa only [d1452, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1452, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1452, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13938 (p : Pattern) (guard : d4670 p = 1) : d1456 p ≤ (0 : Int) + d881 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1456, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13937 p hg
    simpa only [d1456, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1456, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13932 p hg
    simpa only [d1456, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13939 (p : Pattern) (guard : d4670 p = 1) : d1458 p ≤ (0 : Int) + d882 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1458, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13938 p hg
    simpa only [d1458, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1458, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1458, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13940 (p : Pattern) (guard : d4670 p = 1) : d1459 p ≤ (0 : Int) + d883 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1459, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13934 p hg
    simpa only [d1459, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1459, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13939 p hg
    simpa only [d1459, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13941 (p : Pattern) (guard : d0 p = 1) : d1439 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13942 (p : Pattern) (guard : d4670 p = 1) : d1440 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1440, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1440, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1440, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13941 p hg
    simpa only [d4670, d1440, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13943 (p : Pattern) (guard : d4670 p = 1) : d1443 p ≤ (0 : Int) + d885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1443, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13942 p hg
    simpa only [d1443, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1443, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13916 p hg
    simpa only [d1443, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13944 (p : Pattern) (guard : d4670 p = 1) : d1460 p ≤ (0 : Int) + d886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1460, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13930 p hg
    simpa only [d4670, d1460, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1460, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d4670, d1460, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13945 (p : Pattern) (guard : d4670 p = 1) : d1461 p ≤ (0 : Int) + d887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1461, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13944 p hg
    simpa only [d1461, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1461, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13923 p hg
    simpa only [d1461, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13946 (p : Pattern) (guard : d4670 p = 1) : d1462 p ≤ (0 : Int) + d888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1462, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13943 p hg
    simpa only [d1462, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1462, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13945 p hg
    simpa only [d1462, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13947 (p : Pattern) (guard : d0 p = 1) : d1450 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13948 (p : Pattern) (guard : d4670 p = 1) : d1451 p ≤ (0 : Int) + d889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1451, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1451, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1451, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13947 p hg
    simpa only [d4670, d1451, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13949 (p : Pattern) (guard : d4670 p = 1) : d1452 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1452, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13948 p hg
    simpa only [d1452, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1452, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1452, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13950 (p : Pattern) (guard : d4670 p = 1) : d1456 p ≤ (0 : Int) + d891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1456, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13949 p hg
    simpa only [d1456, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1456, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13932 p hg
    simpa only [d1456, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13951 (p : Pattern) (guard : d4670 p = 1) : d1463 p ≤ (0 : Int) + d892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1463, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13946 p hg
    simpa only [d1463, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1463, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13950 p hg
    simpa only [d1463, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13952 (p : Pattern) (guard : d4670 p = 1) : d1464 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1464, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13950 p hg
    simpa only [d1464, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1464, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1464, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13953 (p : Pattern) (guard : d4670 p = 1) : d1465 p ≤ (0 : Int) + d894 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1465, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13951 p hg
    simpa only [d1465, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1465, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13952 p hg
    simpa only [d1465, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13954 (p : Pattern) (guard : d4670 p = 1) : d1466 p ≤ (0 : Int) + d895 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1466, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13940 p hg
    simpa only [d1466, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1466, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13953 p hg
    simpa only [d1466, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13955 (p : Pattern) (guard : d4670 p = 1) : d1467 p ≤ (0 : Int) + d896 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1467, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13884 p hg
    simpa only [d1467, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1467, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13954 p hg
    simpa only [d1467, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13956 (p : Pattern) (guard : d4670 p = 1) : d1468 p ≤ (0 : Int) + d897 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1468, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13911 p hg
    simpa only [d1468, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1468, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13955 p hg
    simpa only [d1468, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13957 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13958 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13957 p hg
    simpa only [d4395, d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13959 (p : Pattern) (guard : d4670 p = 1) : d1412 p ≤ (0 : Int) + d898 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1412, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13958 p hg
    simpa only [d4670, d1412, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1412, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13877 p hg
    simpa only [d4670, d1412, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13960 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d194 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13961 (p : Pattern) (guard : d4395 p = 1) : d1413 p ≤ (0 : Int) + d899 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1413, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d1413, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1413, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13960 p hg
    simpa only [d4395, d1413, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13962 (p : Pattern) (guard : d4670 p = 1) : d1414 p ≤ (0 : Int) + d900 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1414, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13961 p hg
    simpa only [d4670, d1414, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1414, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1414, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13963 (p : Pattern) (guard : d4670 p = 1) : d1415 p ≤ (0 : Int) + d901 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1415, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13959 p hg
    simpa only [d1415, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1415, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13962 p hg
    simpa only [d1415, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13964 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d198 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13965 (p : Pattern) (guard : d4395 p = 1) : d1469 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d1469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13964 p hg
    simpa only [d4395, d1469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13966 (p : Pattern) (guard : d4670 p = 1) : d1470 p ≤ (0 : Int) + d902 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1470, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13965 p hg
    simpa only [d4670, d1470, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1470, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d4670, d1470, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13967 (p : Pattern) (guard : d4670 p = 1) : d1471 p ≤ (0 : Int) + d905 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1471, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13966 p hg
    simpa only [d1471, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1471, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8848 p hg
    simpa only [d1471, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13968 (p : Pattern) (guard : d4670 p = 1) : d1472 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1472, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13963 p hg
    simpa only [d1472, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1472, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13967 p hg
    simpa only [d1472, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13969 (p : Pattern) (guard : d4670 p = 1) : d1473 p ≤ (0 : Int) + d907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1473, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13907 p hg
    simpa only [d1473, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1473, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13968 p hg
    simpa only [d1473, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13970 (p : Pattern) (guard : d4670 p = 1) : d1474 p ≤ (0 : Int) + d908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1474, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13968 p hg
    simpa only [d1474, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1474, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1474, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13971 (p : Pattern) (guard : d4670 p = 1) : d1475 p ≤ (0 : Int) + d909 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1475, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13969 p hg
    simpa only [d1475, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1475, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13970 p hg
    simpa only [d1475, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13972 (p : Pattern) (guard : d4670 p = 1) : d1476 p ≤ (0 : Int) + d910 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1476, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13900 p hg
    simpa only [d1476, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1476, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13971 p hg
    simpa only [d1476, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13973 (p : Pattern) (guard : d4670 p = 1) : d1477 p ≤ (0 : Int) + d911 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1477, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13884 p hg
    simpa only [d1477, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1477, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13972 p hg
    simpa only [d1477, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13974 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13975 (p : Pattern) (guard : d4395 p = 1) : d1453 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1453, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1453, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1453, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13974 p hg
    simpa only [d4395, d1453, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13976 (p : Pattern) (guard : d4670 p = 1) : d1460 p ≤ (0 : Int) + d912 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1460, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13975 p hg
    simpa only [d4670, d1460, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1460, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8858 p hg
    simpa only [d4670, d1460, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13977 (p : Pattern) (guard : d4670 p = 1) : d1461 p ≤ (0 : Int) + d913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1461, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13976 p hg
    simpa only [d1461, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1461, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13923 p hg
    simpa only [d1461, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13978 (p : Pattern) (guard : d4670 p = 1) : d1462 p ≤ (0 : Int) + d914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1462, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13917 p hg
    simpa only [d1462, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1462, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13977 p hg
    simpa only [d1462, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13979 (p : Pattern) (guard : d4670 p = 1) : d1454 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1454, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13975 p hg
    simpa only [d4670, d1454, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1454, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d4670, d1454, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13980 (p : Pattern) (guard : d4670 p = 1) : d1455 p ≤ (0 : Int) + d916 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1455, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13979 p hg
    simpa only [d1455, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1455, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1455, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13981 (p : Pattern) (guard : d4670 p = 1) : d1456 p ≤ (0 : Int) + d917 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1456, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13928 p hg
    simpa only [d1456, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1456, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13980 p hg
    simpa only [d1456, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13982 (p : Pattern) (guard : d4670 p = 1) : d1463 p ≤ (0 : Int) + d918 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1463, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13978 p hg
    simpa only [d1463, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1463, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13981 p hg
    simpa only [d1463, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13983 (p : Pattern) (guard : d4670 p = 1) : d1456 p ≤ (0 : Int) + d919 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1456, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13937 p hg
    simpa only [d1456, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1456, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13980 p hg
    simpa only [d1456, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13984 (p : Pattern) (guard : d4670 p = 1) : d1458 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1458, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13983 p hg
    simpa only [d1458, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1458, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1458, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13985 (p : Pattern) (guard : d4670 p = 1) : d1478 p ≤ (0 : Int) + d921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1478, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13982 p hg
    simpa only [d1478, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1478, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13984 p hg
    simpa only [d1478, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13986 (p : Pattern) (guard : d0 p = 1) : d1479 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13987 (p : Pattern) (guard : d4670 p = 1) : d1480 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1480, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d1480, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1480, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13986 p hg
    simpa only [d4670, d1480, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13988 (p : Pattern) (guard : d0 p = 1) : d275 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13989 (p : Pattern) (guard : d4395 p = 1) : d1481 p ≤ (0 : Int) + d922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1481, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d1481, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1481, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13988 p hg
    simpa only [d4395, d1481, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13990 (p : Pattern) (guard : d0 p = 1) : d279 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13991 (p : Pattern) (guard : d4670 p = 1) : d1482 p ≤ (0 : Int) + d923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1482, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13989 p hg
    simpa only [d4670, d1482, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1482, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13990 p hg
    simpa only [d4670, d1482, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13992 (p : Pattern) (guard : d4670 p = 1) : d1483 p ≤ (0 : Int) + d924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1483, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13987 p hg
    simpa only [d1483, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1483, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13991 p hg
    simpa only [d1483, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13993 (p : Pattern) (guard : d4670 p = 1) : d1484 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1484, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13975 p hg
    simpa only [d4670, d1484, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1484, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8877 p hg
    simpa only [d4670, d1484, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13994 (p : Pattern) (guard : d0 p = 1) : d1375 p ≤ (0 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13995 (p : Pattern) (guard : d4395 p = 1) : d1485 p ≤ (0 : Int) + d926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1485, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d1485, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1485, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13994 p hg
    simpa only [d4395, d1485, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13996 (p : Pattern) (guard : d4670 p = 1) : d1486 p ≤ (0 : Int) + d927 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1486, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13995 p hg
    simpa only [d4670, d1486, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1486, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8881 p hg
    simpa only [d4670, d1486, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13997 (p : Pattern) (guard : d4670 p = 1) : d1487 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1487, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13993 p hg
    simpa only [d1487, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1487, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13996 p hg
    simpa only [d1487, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13998 (p : Pattern) (guard : d4670 p = 1) : d1488 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1488, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13992 p hg
    simpa only [d1488, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1488, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13997 p hg
    simpa only [d1488, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13999 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d241 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
