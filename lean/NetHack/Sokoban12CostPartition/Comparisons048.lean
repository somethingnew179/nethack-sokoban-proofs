/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6720 (p : Pattern) (guard : d1336 p = 1) : d570 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d1336, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d1336, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6721 (p : Pattern) (guard : d0 p = 1) : d560 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6722 (p : Pattern) (guard : d1326 p = 1) : d571 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d1326, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6721 p hg
    simpa only [d1326, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6723 (p : Pattern) (guard : d1329 p = 1) : d572 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6722 p hg
    simpa only [d1329, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d1329, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6724 (p : Pattern) (guard : d1332 p = 1) : d573 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6723 p hg
    simpa only [d1332, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1332, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6725 (p : Pattern) (guard : d0 p = 1) : d576 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6726 (p : Pattern) (guard : d1335 p = 1) : d577 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6724 p hg
    simpa only [d1335, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6725 p hg
    simpa only [d1335, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6727 (p : Pattern) (guard : d1338 p = 1) : d578 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6726 p hg
    simpa only [d1338, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d1338, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6728 (p : Pattern) (guard : d1339 p = 1) : d579 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d1339, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d1339, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6729 (p : Pattern) (guard : d1332 p = 1) : d580 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d1332, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1332, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6730 (p : Pattern) (guard : d0 p = 1) : d581 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6731 (p : Pattern) (guard : d1335 p = 1) : d582 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6729 p hg
    simpa only [d1335, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d1335, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6732 (p : Pattern) (guard : d1338 p = 1) : d583 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6731 p hg
    simpa only [d1338, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d1338, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6733 (p : Pattern) (guard : d1341 p = 1) : d584 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d1341, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d1341, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6734 (p : Pattern) (guard : d1342 p = 1) : d585 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6728 p hg
    simpa only [d1342, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6733 p hg
    simpa only [d1342, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6735 (p : Pattern) (guard : d1343 p = 1) : d586 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d586, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6713 p hg
    simpa only [d1343, d586, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d586, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6734 p hg
    simpa only [d1343, d586, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6736 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare6737 (p : Pattern) (guard : d1309 p = 1) : d28 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1309, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d1309, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6738 (p : Pattern) (guard : d1310 p = 1) : d29 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1310, d29, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6736 p hg
    simpa only [d1310, d29, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1309 p = 1 := by simpa only [d1310, d29, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6737 p hg
    simpa only [d1310, d29, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6739 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6740 (p : Pattern) (guard : d1309 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6741 (p : Pattern) (guard : d1311 p = 1) : d28 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1311, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1311, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6742 (p : Pattern) (guard : d1312 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6740 p hg
    simpa only [d1312, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6741 p hg
    simpa only [d1312, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6743 (p : Pattern) (guard : d1313 p = 1) : d29 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6738 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6742 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6744 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6745 (p : Pattern) (guard : d1314 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6343 p hg
    simpa only [d1314, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d1314, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6746 (p : Pattern) (guard : d1315 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6742 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6745 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6747 (p : Pattern) (guard : d1316 p = 1) : d29 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6748 (p : Pattern) (guard : d1309 p = 1) : d14 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d14, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1309, d14, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d14, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6200 p hg
    simpa only [d1309, d14, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6749 (p : Pattern) (guard : d1311 p = 1) : d28 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d1311, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1311, d28, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6750 (p : Pattern) (guard : d1312 p = 1) : d30 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d30, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d1312, d30, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d30, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d1312, d30, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6751 (p : Pattern) (guard : d1311 p = 1) : d14 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1311, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d1311, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6752 (p : Pattern) (guard : d1314 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d1314, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d1314, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6753 (p : Pattern) (guard : d1315 p = 1) : d30 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6750 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6752 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6754 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6755 (p : Pattern) (guard : d1317 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6752 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6756 (p : Pattern) (guard : d1318 p = 1) : d30 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6753 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6755 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6757 (p : Pattern) (guard : d1319 p = 1) : d31 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d1319, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d1319, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6758 (p : Pattern) (guard : d1314 p = 1) : d588 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d1314, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d1314, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6759 (p : Pattern) (guard : d0 p = 1) : d588 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6760 (p : Pattern) (guard : d1317 p = 1) : d588 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6761 (p : Pattern) (guard : d1318 p = 1) : d589 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d1318, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d1318, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6762 (p : Pattern) (guard : d0 p = 1) : d590 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6763 (p : Pattern) (guard : d1320 p = 1) : d591 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6755 p hg
    simpa only [d1320, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d1320, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6764 (p : Pattern) (guard : d1321 p = 1) : d592 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6761 p hg
    simpa only [d1321, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d1321, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6765 (p : Pattern) (guard : d1322 p = 1) : d593 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d593, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6757 p hg
    simpa only [d1322, d593, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d593, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6764 p hg
    simpa only [d1322, d593, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6766 (p : Pattern) (guard : d0 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6767 (p : Pattern) (guard : d1317 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6745 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6766 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6768 (p : Pattern) (guard : d1318 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6769 (p : Pattern) (guard : d1320 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6755 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6770 (p : Pattern) (guard : d1321 p = 1) : d31 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6768 p hg
    simpa only [d1321, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6769 p hg
    simpa only [d1321, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6771 (p : Pattern) (guard : d1320 p = 1) : d589 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d1320, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d1320, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6772 (p : Pattern) (guard : d0 p = 1) : d591 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6773 (p : Pattern) (guard : d1323 p = 1) : d592 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6771 p hg
    simpa only [d1323, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6772 p hg
    simpa only [d1323, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6774 (p : Pattern) (guard : d1324 p = 1) : d593 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6770 p hg
    simpa only [d1324, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d1324, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6775 (p : Pattern) (guard : d1325 p = 1) : d593 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6765 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6776 (p : Pattern) (guard : d1320 p = 1) : d29 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6766 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6777 (p : Pattern) (guard : d1323 p = 1) : d31 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6776 p hg
    simpa only [d1323, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d1323, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6778 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6779 (p : Pattern) (guard : d1326 p = 1) : d593 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6777 p hg
    simpa only [d1326, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6778 p hg
    simpa only [d1326, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6780 (p : Pattern) (guard : d1327 p = 1) : d593 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6779 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6781 (p : Pattern) (guard : d1328 p = 1) : d593 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6775 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6782 (p : Pattern) (guard : d1311 p = 1) : d32 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d32, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d1311, d32, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d32, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d1311, d32, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6783 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6784 (p : Pattern) (guard : d1314 p = 1) : d32 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6782 p hg
    simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6783 p hg
    simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6785 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6786 (p : Pattern) (guard : d1317 p = 1) : d32 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6784 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6787 (p : Pattern) (guard : d1320 p = 1) : d32 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6786 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6788 (p : Pattern) (guard : d1321 p = 1) : d33 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d1321, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6787 p hg
    simpa only [d1321, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6789 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6790 (p : Pattern) (guard : d1323 p = 1) : d596 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d1323, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d1323, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6791 (p : Pattern) (guard : d1324 p = 1) : d597 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d597, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6788 p hg
    simpa only [d1324, d597, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d597, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6790 p hg
    simpa only [d1324, d597, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6792 (p : Pattern) (guard : d1323 p = 1) : d33 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6769 p hg
    simpa only [d1323, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d1323, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6793 (p : Pattern) (guard : d0 p = 1) : d596 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6794 (p : Pattern) (guard : d1326 p = 1) : d597 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d1326, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6793 p hg
    simpa only [d1326, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6795 (p : Pattern) (guard : d1327 p = 1) : d597 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6791 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6794 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6796 (p : Pattern) (guard : d0 p = 1) : d597 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6797 (p : Pattern) (guard : d1329 p = 1) : d597 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6794 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6796 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6798 (p : Pattern) (guard : d1330 p = 1) : d597 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6795 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6799 (p : Pattern) (guard : d1331 p = 1) : d598 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6781 p hg
    simpa only [d1331, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d1331, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6800 (p : Pattern) (guard : d1320 p = 1) : d588 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6801 (p : Pattern) (guard : d1323 p = 1) : d599 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d1323, d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d1323, d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6802 (p : Pattern) (guard : d1324 p = 1) : d600 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6770 p hg
    simpa only [d1324, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6801 p hg
    simpa only [d1324, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6803 (p : Pattern) (guard : d0 p = 1) : d599 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6804 (p : Pattern) (guard : d1326 p = 1) : d600 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6777 p hg
    simpa only [d1326, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1326, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6805 (p : Pattern) (guard : d1327 p = 1) : d600 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6802 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6804 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6806 (p : Pattern) (guard : d0 p = 1) : d606 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6807 (p : Pattern) (guard : d1329 p = 1) : d607 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6804 p hg
    simpa only [d1329, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6806 p hg
    simpa only [d1329, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6808 (p : Pattern) (guard : d1330 p = 1) : d608 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6805 p hg
    simpa only [d1330, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6807 p hg
    simpa only [d1330, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6809 (p : Pattern) (guard : d0 p = 1) : d609 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6810 (p : Pattern) (guard : d1326 p = 1) : d610 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d1326, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6809 p hg
    simpa only [d1326, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6811 (p : Pattern) (guard : d0 p = 1) : d610 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6812 (p : Pattern) (guard : d1329 p = 1) : d610 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6811 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6813 (p : Pattern) (guard : d0 p = 1) : d615 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6814 (p : Pattern) (guard : d1332 p = 1) : d616 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6812 p hg
    simpa only [d1332, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d1332, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6815 (p : Pattern) (guard : d1333 p = 1) : d617 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6808 p hg
    simpa only [d1333, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6814 p hg
    simpa only [d1333, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6816 (p : Pattern) (guard : d1334 p = 1) : d618 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d618, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6799 p hg
    simpa only [d1334, d618, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d618, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6815 p hg
    simpa only [d1334, d618, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6817 (p : Pattern) (guard : d1326 p = 1) : d599 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6801 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6818 (p : Pattern) (guard : d1329 p = 1) : d599 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6817 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6819 (p : Pattern) (guard : d1330 p = 1) : d619 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d1330, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6818 p hg
    simpa only [d1330, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6820 (p : Pattern) (guard : d1332 p = 1) : d620 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d1332, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6809 p hg
    simpa only [d1332, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6821 (p : Pattern) (guard : d1333 p = 1) : d621 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6819 p hg
    simpa only [d1333, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6820 p hg
    simpa only [d1333, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6822 (p : Pattern) (guard : d1332 p = 1) : d622 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6807 p hg
    simpa only [d1332, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1332, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6823 (p : Pattern) (guard : d0 p = 1) : d623 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6824 (p : Pattern) (guard : d1335 p = 1) : d624 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6822 p hg
    simpa only [d1335, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d1335, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6825 (p : Pattern) (guard : d1336 p = 1) : d625 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d1336, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6824 p hg
    simpa only [d1336, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6826 (p : Pattern) (guard : d1337 p = 1) : d626 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d626, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6816 p hg
    simpa only [d1337, d626, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d626, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6825 p hg
    simpa only [d1337, d626, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6827 (p : Pattern) (guard : d1332 p = 1) : d599 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6818 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6828 (p : Pattern) (guard : d1335 p = 1) : d627 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6827 p hg
    simpa only [d1335, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6809 p hg
    simpa only [d1335, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6829 (p : Pattern) (guard : d0 p = 1) : d627 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6830 (p : Pattern) (guard : d1338 p = 1) : d627 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6828 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6831 (p : Pattern) (guard : d1339 p = 1) : d628 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6825 p hg
    simpa only [d1339, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6830 p hg
    simpa only [d1339, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6832 (p : Pattern) (guard : d1340 p = 1) : d629 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d629, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6826 p hg
    simpa only [d1340, d629, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d629, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6831 p hg
    simpa only [d1340, d629, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6833 (p : Pattern) (guard : d0 p = 1) : d633 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6834 (p : Pattern) (guard : d1329 p = 1) : d634 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6779 p hg
    simpa only [d1329, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6833 p hg
    simpa only [d1329, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6835 (p : Pattern) (guard : d1330 p = 1) : d635 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d1330, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6834 p hg
    simpa only [d1330, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6836 (p : Pattern) (guard : d0 p = 1) : d639 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6837 (p : Pattern) (guard : d1332 p = 1) : d640 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d1332, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6836 p hg
    simpa only [d1332, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6838 (p : Pattern) (guard : d1333 p = 1) : d641 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6835 p hg
    simpa only [d1333, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6837 p hg
    simpa only [d1333, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6839 (p : Pattern) (guard : d1336 p = 1) : d642 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6838 p hg
    simpa only [d1336, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6828 p hg
    simpa only [d1336, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6840 (p : Pattern) (guard : d0 p = 1) : d632 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6841 (p : Pattern) (guard : d1326 p = 1) : d643 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6777 p hg
    simpa only [d1326, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6840 p hg
    simpa only [d1326, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6842 (p : Pattern) (guard : d1329 p = 1) : d644 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6841 p hg
    simpa only [d1329, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6833 p hg
    simpa only [d1329, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6843 (p : Pattern) (guard : d1332 p = 1) : d645 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6842 p hg
    simpa only [d1332, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1332, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6844 (p : Pattern) (guard : d0 p = 1) : d648 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6845 (p : Pattern) (guard : d1335 p = 1) : d649 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6843 p hg
    simpa only [d1335, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6844 p hg
    simpa only [d1335, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6846 (p : Pattern) (guard : d1338 p = 1) : d650 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6845 p hg
    simpa only [d1338, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d1338, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6847 (p : Pattern) (guard : d1339 p = 1) : d651 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6839 p hg
    simpa only [d1339, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6846 p hg
    simpa only [d1339, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6848 (p : Pattern) (guard : d1332 p = 1) : d652 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6834 p hg
    simpa only [d1332, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d1332, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6849 (p : Pattern) (guard : d0 p = 1) : d653 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6850 (p : Pattern) (guard : d1335 p = 1) : d654 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6848 p hg
    simpa only [d1335, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6849 p hg
    simpa only [d1335, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6851 (p : Pattern) (guard : d1338 p = 1) : d655 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d1338, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d1338, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6852 (p : Pattern) (guard : d1341 p = 1) : d656 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6851 p hg
    simpa only [d1341, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d1341, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6853 (p : Pattern) (guard : d1342 p = 1) : d657 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6847 p hg
    simpa only [d1342, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6852 p hg
    simpa only [d1342, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6854 (p : Pattern) (guard : d1343 p = 1) : d658 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d658, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6832 p hg
    simpa only [d1343, d658, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d658, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6853 p hg
    simpa only [d1343, d658, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6855 (p : Pattern) (guard : d1337 p = 1) : d210 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d210, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d1337, d210, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d210, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6525 p hg
    simpa only [d1337, d210, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6856 (p : Pattern) (guard : d1332 p = 1) : d211 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d1332, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6857 (p : Pattern) (guard : d0 p = 1) : d212 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6858 (p : Pattern) (guard : d1335 p = 1) : d213 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6856 p hg
    simpa only [d1335, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6857 p hg
    simpa only [d1335, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6859 (p : Pattern) (guard : d1336 p = 1) : d214 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d1336, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6858 p hg
    simpa only [d1336, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
