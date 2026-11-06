/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7280 (p : Pattern) (guard : d1340 p = 1) : d316 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d316, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d1340, d316, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d316, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d1340, d316, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7281 (p : Pattern) (guard : d1339 p = 1) : d317 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d1339, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d1339, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7282 (p : Pattern) (guard : d1342 p = 1) : d318 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d1342, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d1342, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7283 (p : Pattern) (guard : d1343 p = 1) : d319 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d319, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7280 p hg
    simpa only [d1343, d319, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d319, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d1343, d319, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
