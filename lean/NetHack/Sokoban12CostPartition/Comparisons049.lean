/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6860 (p : Pattern) (guard : d1339 p = 1) : d215 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6859 p hg
    simpa only [d1339, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6861 (p : Pattern) (guard : d1340 p = 1) : d216 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d216, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6855 p hg
    simpa only [d1340, d216, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d216, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6860 p hg
    simpa only [d1340, d216, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6862 (p : Pattern) (guard : d1339 p = 1) : d217 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d1339, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6863 (p : Pattern) (guard : d1342 p = 1) : d218 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6862 p hg
    simpa only [d1342, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d1342, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6864 (p : Pattern) (guard : d1343 p = 1) : d219 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d219, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6861 p hg
    simpa only [d1343, d219, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d219, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6863 p hg
    simpa only [d1343, d219, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6865 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6866 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d36, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6865 p hg
    simpa only [d36, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6867 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d3 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6868 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6869 (p : Pattern) (guard : d1233 p = 1) : d9 p ≤ (0 : Int) + d5 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6868 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6870 (p : Pattern) (guard : d1309 p = 1) : d37 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6867 p hg
    simpa only [d1309, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6869 p hg
    simpa only [d1309, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6871 (p : Pattern) (guard : d1310 p = 1) : d38 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1310, d38, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d1310, d38, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1309 p = 1 := by simpa only [d1310, d38, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6870 p hg
    simpa only [d1310, d38, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6872 (p : Pattern) (guard : d1233 p = 1) : d35 p ≤ (0 : Int) + d5 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1233, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6873 (p : Pattern) (guard : d1309 p = 1) : d36 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1309, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6872 p hg
    simpa only [d1309, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6874 (p : Pattern) (guard : d1233 p = 1) : d16 p ≤ (0 : Int) + d5 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6875 (p : Pattern) (guard : d1311 p = 1) : d37 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6874 p hg
    simpa only [d1311, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d1311, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6876 (p : Pattern) (guard : d1312 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6873 p hg
    simpa only [d1312, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6875 p hg
    simpa only [d1312, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6877 (p : Pattern) (guard : d1313 p = 1) : d38 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6878 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6879 (p : Pattern) (guard : d1311 p = 1) : d36 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1311, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d1311, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6880 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6881 (p : Pattern) (guard : d1314 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6879 p hg
    simpa only [d1314, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6880 p hg
    simpa only [d1314, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6882 (p : Pattern) (guard : d1315 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6881 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6883 (p : Pattern) (guard : d1316 p = 1) : d38 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6877 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6882 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6884 (p : Pattern) (guard : d1233 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6885 (p : Pattern) (guard : d1309 p = 1) : d39 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d39, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1309, d39, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d39, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6884 p hg
    simpa only [d1309, d39, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6886 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6887 (p : Pattern) (guard : d1233 p = 1) : d16 p ≤ (0 : Int) + d3 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d1233, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6888 (p : Pattern) (guard : d1311 p = 1) : d37 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6887 p hg
    simpa only [d1311, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d1311, d37, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6889 (p : Pattern) (guard : d1312 p = 1) : d40 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d40, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6885 p hg
    simpa only [d1312, d40, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d40, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6888 p hg
    simpa only [d1312, d40, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6890 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6891 (p : Pattern) (guard : d1311 p = 1) : d39 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1311, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6890 p hg
    simpa only [d1311, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6892 (p : Pattern) (guard : d1314 p = 1) : d40 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6891 p hg
    simpa only [d1314, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6880 p hg
    simpa only [d1314, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6893 (p : Pattern) (guard : d1315 p = 1) : d40 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6889 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6892 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6894 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6895 (p : Pattern) (guard : d1317 p = 1) : d40 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6892 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6896 (p : Pattern) (guard : d1318 p = 1) : d40 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6893 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6895 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6897 (p : Pattern) (guard : d1319 p = 1) : d41 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6883 p hg
    simpa only [d1319, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6896 p hg
    simpa only [d1319, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6898 (p : Pattern) (guard : d0 p = 1) : d659 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6899 (p : Pattern) (guard : d1311 p = 1) : d660 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d1311, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6898 p hg
    simpa only [d1311, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6900 (p : Pattern) (guard : d0 p = 1) : d661 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6901 (p : Pattern) (guard : d1314 p = 1) : d662 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6899 p hg
    simpa only [d1314, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d1314, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6902 (p : Pattern) (guard : d0 p = 1) : d662 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6903 (p : Pattern) (guard : d1317 p = 1) : d662 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6901 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6904 (p : Pattern) (guard : d1318 p = 1) : d663 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6882 p hg
    simpa only [d1318, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6903 p hg
    simpa only [d1318, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6905 (p : Pattern) (guard : d0 p = 1) : d665 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6906 (p : Pattern) (guard : d1320 p = 1) : d666 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6895 p hg
    simpa only [d1320, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6905 p hg
    simpa only [d1320, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6907 (p : Pattern) (guard : d1321 p = 1) : d667 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6904 p hg
    simpa only [d1321, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6906 p hg
    simpa only [d1321, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6908 (p : Pattern) (guard : d1322 p = 1) : d668 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d668, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6897 p hg
    simpa only [d1322, d668, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d668, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6907 p hg
    simpa only [d1322, d668, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6909 (p : Pattern) (guard : d0 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6910 (p : Pattern) (guard : d1317 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6881 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6909 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6911 (p : Pattern) (guard : d1318 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6882 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6910 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6912 (p : Pattern) (guard : d1320 p = 1) : d40 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6895 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6913 (p : Pattern) (guard : d1321 p = 1) : d41 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6911 p hg
    simpa only [d1321, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6912 p hg
    simpa only [d1321, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6914 (p : Pattern) (guard : d1320 p = 1) : d663 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6910 p hg
    simpa only [d1320, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d1320, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6915 (p : Pattern) (guard : d0 p = 1) : d666 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6916 (p : Pattern) (guard : d1323 p = 1) : d667 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6914 p hg
    simpa only [d1323, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6915 p hg
    simpa only [d1323, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6917 (p : Pattern) (guard : d1324 p = 1) : d668 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6913 p hg
    simpa only [d1324, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6916 p hg
    simpa only [d1324, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6918 (p : Pattern) (guard : d1325 p = 1) : d668 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6908 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6917 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6919 (p : Pattern) (guard : d1320 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6910 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6909 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6920 (p : Pattern) (guard : d1323 p = 1) : d41 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6919 p hg
    simpa only [d1323, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d1323, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6921 (p : Pattern) (guard : d0 p = 1) : d667 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6922 (p : Pattern) (guard : d1326 p = 1) : d668 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6920 p hg
    simpa only [d1326, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6921 p hg
    simpa only [d1326, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6923 (p : Pattern) (guard : d1327 p = 1) : d668 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6917 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6922 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6924 (p : Pattern) (guard : d1328 p = 1) : d668 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6918 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6925 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6926 (p : Pattern) (guard : d1311 p = 1) : d16 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6925 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6927 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6928 (p : Pattern) (guard : d1314 p = 1) : d42 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d42, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6926 p hg
    simpa only [d1314, d42, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d42, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6927 p hg
    simpa only [d1314, d42, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6929 (p : Pattern) (guard : d0 p = 1) : d42 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6930 (p : Pattern) (guard : d1317 p = 1) : d42 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6928 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6929 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6931 (p : Pattern) (guard : d1320 p = 1) : d42 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6930 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6929 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6932 (p : Pattern) (guard : d1321 p = 1) : d43 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6896 p hg
    simpa only [d1321, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6931 p hg
    simpa only [d1321, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6933 (p : Pattern) (guard : d0 p = 1) : d670 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6934 (p : Pattern) (guard : d1323 p = 1) : d671 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6906 p hg
    simpa only [d1323, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6933 p hg
    simpa only [d1323, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6935 (p : Pattern) (guard : d1324 p = 1) : d672 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d672, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6932 p hg
    simpa only [d1324, d672, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d672, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6934 p hg
    simpa only [d1324, d672, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6936 (p : Pattern) (guard : d1323 p = 1) : d43 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6912 p hg
    simpa only [d1323, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6929 p hg
    simpa only [d1323, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6937 (p : Pattern) (guard : d0 p = 1) : d671 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6938 (p : Pattern) (guard : d1326 p = 1) : d672 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6936 p hg
    simpa only [d1326, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6937 p hg
    simpa only [d1326, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6939 (p : Pattern) (guard : d1327 p = 1) : d672 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6935 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6938 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6940 (p : Pattern) (guard : d0 p = 1) : d672 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6941 (p : Pattern) (guard : d1329 p = 1) : d672 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6938 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6940 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6942 (p : Pattern) (guard : d1330 p = 1) : d672 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6939 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6941 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6943 (p : Pattern) (guard : d1331 p = 1) : d673 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6924 p hg
    simpa only [d1331, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6942 p hg
    simpa only [d1331, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6944 (p : Pattern) (guard : d1320 p = 1) : d662 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6903 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6945 (p : Pattern) (guard : d1323 p = 1) : d674 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6944 p hg
    simpa only [d1323, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6905 p hg
    simpa only [d1323, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6946 (p : Pattern) (guard : d1324 p = 1) : d675 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6913 p hg
    simpa only [d1324, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6945 p hg
    simpa only [d1324, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6947 (p : Pattern) (guard : d0 p = 1) : d674 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6948 (p : Pattern) (guard : d1326 p = 1) : d675 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6920 p hg
    simpa only [d1326, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1326, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6949 (p : Pattern) (guard : d1327 p = 1) : d675 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6946 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6948 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6950 (p : Pattern) (guard : d0 p = 1) : d681 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6951 (p : Pattern) (guard : d1329 p = 1) : d682 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6948 p hg
    simpa only [d1329, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6950 p hg
    simpa only [d1329, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6952 (p : Pattern) (guard : d1330 p = 1) : d683 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6949 p hg
    simpa only [d1330, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6951 p hg
    simpa only [d1330, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6953 (p : Pattern) (guard : d0 p = 1) : d684 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6954 (p : Pattern) (guard : d1326 p = 1) : d685 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6936 p hg
    simpa only [d1326, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d1326, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6955 (p : Pattern) (guard : d0 p = 1) : d685 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6956 (p : Pattern) (guard : d1329 p = 1) : d685 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6954 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6955 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6957 (p : Pattern) (guard : d0 p = 1) : d690 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6958 (p : Pattern) (guard : d1332 p = 1) : d691 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6956 p hg
    simpa only [d1332, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6957 p hg
    simpa only [d1332, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6959 (p : Pattern) (guard : d1333 p = 1) : d692 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6952 p hg
    simpa only [d1333, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6958 p hg
    simpa only [d1333, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6960 (p : Pattern) (guard : d1334 p = 1) : d693 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d693, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6943 p hg
    simpa only [d1334, d693, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d693, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d1334, d693, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6961 (p : Pattern) (guard : d1326 p = 1) : d674 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6945 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6962 (p : Pattern) (guard : d1329 p = 1) : d674 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6963 (p : Pattern) (guard : d1330 p = 1) : d694 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d1330, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d1330, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6964 (p : Pattern) (guard : d1332 p = 1) : d695 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6941 p hg
    simpa only [d1332, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d1332, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6965 (p : Pattern) (guard : d1333 p = 1) : d696 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d1333, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d1333, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6966 (p : Pattern) (guard : d1332 p = 1) : d697 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6951 p hg
    simpa only [d1332, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1332, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6967 (p : Pattern) (guard : d0 p = 1) : d698 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6968 (p : Pattern) (guard : d1335 p = 1) : d699 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6966 p hg
    simpa only [d1335, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d1335, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6969 (p : Pattern) (guard : d1336 p = 1) : d700 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6965 p hg
    simpa only [d1336, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6968 p hg
    simpa only [d1336, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6970 (p : Pattern) (guard : d1337 p = 1) : d701 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d701, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6960 p hg
    simpa only [d1337, d701, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d701, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d1337, d701, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6971 (p : Pattern) (guard : d1332 p = 1) : d674 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6972 (p : Pattern) (guard : d1335 p = 1) : d702 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6971 p hg
    simpa only [d1335, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d1335, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6973 (p : Pattern) (guard : d0 p = 1) : d702 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6974 (p : Pattern) (guard : d1338 p = 1) : d702 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6975 (p : Pattern) (guard : d1339 p = 1) : d703 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d1339, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6974 p hg
    simpa only [d1339, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6976 (p : Pattern) (guard : d1340 p = 1) : d704 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d704, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d1340, d704, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d704, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d1340, d704, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6977 (p : Pattern) (guard : d0 p = 1) : d708 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6978 (p : Pattern) (guard : d1329 p = 1) : d709 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6922 p hg
    simpa only [d1329, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6977 p hg
    simpa only [d1329, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6979 (p : Pattern) (guard : d1330 p = 1) : d710 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d1330, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6978 p hg
    simpa only [d1330, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6980 (p : Pattern) (guard : d0 p = 1) : d714 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6981 (p : Pattern) (guard : d1332 p = 1) : d715 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6941 p hg
    simpa only [d1332, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6980 p hg
    simpa only [d1332, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6982 (p : Pattern) (guard : d1333 p = 1) : d716 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6979 p hg
    simpa only [d1333, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d1333, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6983 (p : Pattern) (guard : d1336 p = 1) : d717 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d1336, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d1336, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6984 (p : Pattern) (guard : d0 p = 1) : d707 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6985 (p : Pattern) (guard : d1326 p = 1) : d718 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6920 p hg
    simpa only [d1326, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6984 p hg
    simpa only [d1326, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6986 (p : Pattern) (guard : d1329 p = 1) : d719 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d1329, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6977 p hg
    simpa only [d1329, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6987 (p : Pattern) (guard : d1332 p = 1) : d720 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6986 p hg
    simpa only [d1332, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1332, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6988 (p : Pattern) (guard : d0 p = 1) : d723 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6989 (p : Pattern) (guard : d1335 p = 1) : d724 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6987 p hg
    simpa only [d1335, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6988 p hg
    simpa only [d1335, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6990 (p : Pattern) (guard : d1338 p = 1) : d725 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6989 p hg
    simpa only [d1338, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d1338, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6991 (p : Pattern) (guard : d1339 p = 1) : d726 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d1339, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6990 p hg
    simpa only [d1339, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6992 (p : Pattern) (guard : d1332 p = 1) : d727 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6978 p hg
    simpa only [d1332, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d1332, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6993 (p : Pattern) (guard : d0 p = 1) : d728 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6994 (p : Pattern) (guard : d1335 p = 1) : d729 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6992 p hg
    simpa only [d1335, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6993 p hg
    simpa only [d1335, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6995 (p : Pattern) (guard : d1338 p = 1) : d730 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d1338, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d1338, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6996 (p : Pattern) (guard : d1341 p = 1) : d731 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6995 p hg
    simpa only [d1341, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d1341, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6997 (p : Pattern) (guard : d1342 p = 1) : d732 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6991 p hg
    simpa only [d1342, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d1342, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6998 (p : Pattern) (guard : d1343 p = 1) : d733 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d733, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6976 p hg
    simpa only [d1343, d733, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d733, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6997 p hg
    simpa only [d1343, d733, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6999 (p : Pattern) (guard : d1339 p = 1) : d135 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d1339, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
