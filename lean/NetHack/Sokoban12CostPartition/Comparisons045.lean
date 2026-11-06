/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6300 (p : Pattern) (guard : d1316 p = 1) : d0 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6299 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6301 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare6302 (p : Pattern) (guard : d1309 p = 1) : d0 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6301 p hg
    simpa only [d1309, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6303 (p : Pattern) (guard : d1233 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem compare6304 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6305 (p : Pattern) (guard : d1311 p = 1) : d0 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d1311, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6306 (p : Pattern) (guard : d1312 p = 1) : d0 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d1312, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d1312, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6307 (p : Pattern) (guard : d1314 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6308 (p : Pattern) (guard : d1315 p = 1) : d0 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6306 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6307 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6309 (p : Pattern) (guard : d1317 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6310 (p : Pattern) (guard : d1318 p = 1) : d0 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6309 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6311 (p : Pattern) (guard : d1319 p = 1) : d0 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6300 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6312 (p : Pattern) (guard : d1321 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6313 (p : Pattern) (guard : d1322 p = 1) : d0 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6311 p hg
    simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6314 (p : Pattern) (guard : d1324 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6315 (p : Pattern) (guard : d1325 p = 1) : d0 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6313 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6314 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6316 (p : Pattern) (guard : d1327 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6317 (p : Pattern) (guard : d1328 p = 1) : d0 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6316 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6318 (p : Pattern) (guard : d1311 p = 1) : d0 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6319 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6320 (p : Pattern) (guard : d1314 p = 1) : d0 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6318 p hg
    simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6319 p hg
    simpa only [d1314, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6321 (p : Pattern) (guard : d1317 p = 1) : d0 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6320 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6322 (p : Pattern) (guard : d1320 p = 1) : d0 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6321 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6323 (p : Pattern) (guard : d1321 p = 1) : d0 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6322 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6324 (p : Pattern) (guard : d1323 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6325 (p : Pattern) (guard : d1324 p = 1) : d0 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6323 p hg
    simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6324 p hg
    simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6326 (p : Pattern) (guard : d1326 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6327 (p : Pattern) (guard : d1327 p = 1) : d0 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6325 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6328 (p : Pattern) (guard : d1329 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6329 (p : Pattern) (guard : d1330 p = 1) : d0 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6328 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6330 (p : Pattern) (guard : d1331 p = 1) : d0 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6331 (p : Pattern) (guard : d1333 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6332 (p : Pattern) (guard : d1334 p = 1) : d0 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6330 p hg
    simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6331 p hg
    simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6333 (p : Pattern) (guard : d1336 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6334 (p : Pattern) (guard : d1337 p = 1) : d0 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6332 p hg
    simpa only [d1337, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d1337, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6335 (p : Pattern) (guard : d1339 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6336 (p : Pattern) (guard : d1340 p = 1) : d0 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d1340, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d1340, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6337 (p : Pattern) (guard : d1342 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6338 (p : Pattern) (guard : d1343 p = 1) : d0 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6336 p hg
    simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d1343, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6339 (p : Pattern) (guard : d1233 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6340 (p : Pattern) (guard : d1309 p = 1) : d6 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1309, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1309, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d1309, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d1309, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6341 (p : Pattern) (guard : d1310 p = 1) : d7 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1310, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1310, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1309 p = 1 := by simpa only [d1310, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d1310, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6342 (p : Pattern) (guard : d1309 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6343 (p : Pattern) (guard : d1311 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6344 (p : Pattern) (guard : d1312 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d1312, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6343 p hg
    simpa only [d1312, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6345 (p : Pattern) (guard : d1313 p = 1) : d7 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1310 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6341 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1312 p = 1 := by simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d1313, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6346 (p : Pattern) (guard : d1311 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6347 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6348 (p : Pattern) (guard : d1314 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6346 p hg
    simpa only [d1314, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6347 p hg
    simpa only [d1314, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6349 (p : Pattern) (guard : d1315 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6350 (p : Pattern) (guard : d1316 p = 1) : d7 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6345 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d1316, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6351 (p : Pattern) (guard : d1311 p = 1) : d6 p ≤ (0 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d1311, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1311, d6, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6352 (p : Pattern) (guard : d1312 p = 1) : d7 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d1312, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6351 p hg
    simpa only [d1312, d7, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6353 (p : Pattern) (guard : d1315 p = 1) : d7 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6354 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6355 (p : Pattern) (guard : d1317 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6356 (p : Pattern) (guard : d1318 p = 1) : d7 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6357 (p : Pattern) (guard : d1319 p = 1) : d7 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6358 (p : Pattern) (guard : d1311 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem compare6359 (p : Pattern) (guard : d1314 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6358 p hg
    simpa only [d1314, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d1314, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6360 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6361 (p : Pattern) (guard : d1317 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6362 (p : Pattern) (guard : d1318 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d1318, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d1318, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6363 (p : Pattern) (guard : d1320 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d1320, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1320, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6364 (p : Pattern) (guard : d1321 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6362 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6365 (p : Pattern) (guard : d1322 p = 1) : d57 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6357 p hg
    simpa only [d1322, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d1322, d57, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6366 (p : Pattern) (guard : d1318 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6367 (p : Pattern) (guard : d1320 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6368 (p : Pattern) (guard : d1321 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6366 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6369 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6370 (p : Pattern) (guard : d1323 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6371 (p : Pattern) (guard : d1324 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6368 p hg
    simpa only [d1324, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1324, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6372 (p : Pattern) (guard : d1325 p = 1) : d57 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6365 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6373 (p : Pattern) (guard : d1323 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6374 (p : Pattern) (guard : d1326 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d1326, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d1326, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6375 (p : Pattern) (guard : d1327 p = 1) : d57 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6376 (p : Pattern) (guard : d1328 p = 1) : d57 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6377 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6378 (p : Pattern) (guard : d1233 p = 1) : d8 p ≤ (0 : Int) + d0 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6379 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6380 (p : Pattern) (guard : d1311 p = 1) : d8 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d1311, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6381 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d1237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6382 (p : Pattern) (guard : d1314 p = 1) : d11 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d11, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d1314, d11, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d11, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d1314, d11, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6383 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6384 (p : Pattern) (guard : d1317 p = 1) : d11 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6385 (p : Pattern) (guard : d1320 p = 1) : d11 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6386 (p : Pattern) (guard : d1321 p = 1) : d12 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d1321, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6385 p hg
    simpa only [d1321, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6387 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6388 (p : Pattern) (guard : d1323 p = 1) : d62 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d1323, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d1323, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6389 (p : Pattern) (guard : d1324 p = 1) : d63 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d63, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d1324, d63, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d63, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d1324, d63, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6390 (p : Pattern) (guard : d1323 p = 1) : d12 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d1323, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d1323, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6391 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6392 (p : Pattern) (guard : d1326 p = 1) : d63 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d1326, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d1326, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6393 (p : Pattern) (guard : d1327 p = 1) : d63 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6394 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6395 (p : Pattern) (guard : d1329 p = 1) : d63 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6396 (p : Pattern) (guard : d1330 p = 1) : d63 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6393 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6397 (p : Pattern) (guard : d1331 p = 1) : d64 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d1331, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d1331, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6398 (p : Pattern) (guard : d1320 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6399 (p : Pattern) (guard : d1323 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6400 (p : Pattern) (guard : d1324 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6368 p hg
    simpa only [d1324, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1324, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6401 (p : Pattern) (guard : d1326 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d1326, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1326, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6402 (p : Pattern) (guard : d1327 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6403 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6404 (p : Pattern) (guard : d1329 p = 1) : d122 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d1329, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6403 p hg
    simpa only [d1329, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6405 (p : Pattern) (guard : d1330 p = 1) : d179 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d1330, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1330, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6406 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6407 (p : Pattern) (guard : d1326 p = 1) : d109 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d1326, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1326, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6408 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6409 (p : Pattern) (guard : d1329 p = 1) : d109 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6408 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6410 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6411 (p : Pattern) (guard : d1332 p = 1) : d237 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1332, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6410 p hg
    simpa only [d1332, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6412 (p : Pattern) (guard : d1333 p = 1) : d238 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d1333, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6411 p hg
    simpa only [d1333, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6413 (p : Pattern) (guard : d1334 p = 1) : d239 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d239, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d1334, d239, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d239, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d1334, d239, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6414 (p : Pattern) (guard : d1326 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6415 (p : Pattern) (guard : d1329 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6416 (p : Pattern) (guard : d1330 p = 1) : d68 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1330, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6417 (p : Pattern) (guard : d1332 p = 1) : d69 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1332, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6418 (p : Pattern) (guard : d1333 p = 1) : d70 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d1333, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6417 p hg
    simpa only [d1333, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6419 (p : Pattern) (guard : d1332 p = 1) : d181 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1332, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6420 (p : Pattern) (guard : d0 p = 1) : d240 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6421 (p : Pattern) (guard : d1335 p = 1) : d241 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d1335, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6420 p hg
    simpa only [d1335, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6422 (p : Pattern) (guard : d1336 p = 1) : d242 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d1336, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6421 p hg
    simpa only [d1336, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6423 (p : Pattern) (guard : d1337 p = 1) : d243 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d243, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d1337, d243, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d243, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d1337, d243, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6424 (p : Pattern) (guard : d1332 p = 1) : d55 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6425 (p : Pattern) (guard : d1335 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d1335, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1335, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6426 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6427 (p : Pattern) (guard : d1338 p = 1) : d66 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6428 (p : Pattern) (guard : d1339 p = 1) : d244 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d1339, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6429 (p : Pattern) (guard : d1340 p = 1) : d245 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d245, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6423 p hg
    simpa only [d1340, d245, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d245, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d1340, d245, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6430 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6431 (p : Pattern) (guard : d1329 p = 1) : d153 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d1329, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d1329, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6432 (p : Pattern) (guard : d1330 p = 1) : d186 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1330, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d1330, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6433 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6434 (p : Pattern) (guard : d1332 p = 1) : d246 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1332, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d1332, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6435 (p : Pattern) (guard : d1333 p = 1) : d247 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d1333, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d1333, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6436 (p : Pattern) (guard : d1336 p = 1) : d248 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1336, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6437 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6438 (p : Pattern) (guard : d1326 p = 1) : d138 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d1326, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1326, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6439 (p : Pattern) (guard : d1329 p = 1) : d140 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d1329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d1329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
