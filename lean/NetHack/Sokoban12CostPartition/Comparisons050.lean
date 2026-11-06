/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7000 (p : Pattern) (guard : d1340 p = 1) : d136 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d136, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d1340, d136, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d136, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6999 p hg
    simpa only [d1340, d136, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7001 (p : Pattern) (guard : d1332 p = 1) : d154 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d1332, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d1332, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7002 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7003 (p : Pattern) (guard : d1335 p = 1) : d157 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7001 p hg
    simpa only [d1335, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d1335, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7004 (p : Pattern) (guard : d1338 p = 1) : d158 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7003 p hg
    simpa only [d1338, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7005 (p : Pattern) (guard : d1341 p = 1) : d159 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d1341, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7006 (p : Pattern) (guard : d1342 p = 1) : d160 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d1342, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7005 p hg
    simpa only [d1342, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7007 (p : Pattern) (guard : d1343 p = 1) : d161 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d161, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7000 p hg
    simpa only [d1343, d161, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d161, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d1343, d161, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7008 (p : Pattern) (guard : d1325 p = 1) : d114 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6365 p hg
    simpa only [d1325, d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6516 p hg
    simpa only [d1325, d114, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7009 (p : Pattern) (guard : d1327 p = 1) : d114 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7010 (p : Pattern) (guard : d1328 p = 1) : d114 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7008 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7011 (p : Pattern) (guard : d1327 p = 1) : d116 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d116, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d1327, d116, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d116, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d1327, d116, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7012 (p : Pattern) (guard : d1329 p = 1) : d116 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1329, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1329, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7013 (p : Pattern) (guard : d1330 p = 1) : d116 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7011 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7014 (p : Pattern) (guard : d1331 p = 1) : d335 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7010 p hg
    simpa only [d1331, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7013 p hg
    simpa only [d1331, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7015 (p : Pattern) (guard : d1327 p = 1) : d107 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d1327, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1327, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7016 (p : Pattern) (guard : d1330 p = 1) : d107 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7017 (p : Pattern) (guard : d1329 p = 1) : d110 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d1329, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1329, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7018 (p : Pattern) (guard : d1332 p = 1) : d110 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7017 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7019 (p : Pattern) (guard : d1333 p = 1) : d336 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7016 p hg
    simpa only [d1333, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7018 p hg
    simpa only [d1333, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7020 (p : Pattern) (guard : d1334 p = 1) : d337 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d337, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7014 p hg
    simpa only [d1334, d337, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d337, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d1334, d337, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7021 (p : Pattern) (guard : d1330 p = 1) : d338 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d1330, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7022 (p : Pattern) (guard : d1332 p = 1) : d339 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d1332, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7023 (p : Pattern) (guard : d1333 p = 1) : d340 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7021 p hg
    simpa only [d1333, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7022 p hg
    simpa only [d1333, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7024 (p : Pattern) (guard : d1336 p = 1) : d341 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7023 p hg
    simpa only [d1336, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6858 p hg
    simpa only [d1336, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7025 (p : Pattern) (guard : d1337 p = 1) : d342 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d342, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7020 p hg
    simpa only [d1337, d342, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d342, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d1337, d342, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7026 (p : Pattern) (guard : d1339 p = 1) : d343 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d1339, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7027 (p : Pattern) (guard : d1340 p = 1) : d344 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d344, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d1340, d344, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d344, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7026 p hg
    simpa only [d1340, d344, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7028 (p : Pattern) (guard : d1330 p = 1) : d114 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7029 (p : Pattern) (guard : d1332 p = 1) : d116 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7030 (p : Pattern) (guard : d1333 p = 1) : d335 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1333, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d1333, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7031 (p : Pattern) (guard : d1336 p = 1) : d345 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d1336, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7032 (p : Pattern) (guard : d1329 p = 1) : d346 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d1329, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1329, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7033 (p : Pattern) (guard : d1332 p = 1) : d347 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7032 p hg
    simpa only [d1332, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7034 (p : Pattern) (guard : d0 p = 1) : d349 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7035 (p : Pattern) (guard : d1335 p = 1) : d350 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7033 p hg
    simpa only [d1335, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d1335, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7036 (p : Pattern) (guard : d1338 p = 1) : d351 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7035 p hg
    simpa only [d1338, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7037 (p : Pattern) (guard : d1339 p = 1) : d352 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7031 p hg
    simpa only [d1339, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d1339, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7038 (p : Pattern) (guard : d1332 p = 1) : d338 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d1332, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7039 (p : Pattern) (guard : d0 p = 1) : d339 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7040 (p : Pattern) (guard : d1335 p = 1) : d340 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d1335, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d1335, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7041 (p : Pattern) (guard : d1338 p = 1) : d353 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d1338, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7042 (p : Pattern) (guard : d1341 p = 1) : d354 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7041 p hg
    simpa only [d1341, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7043 (p : Pattern) (guard : d1342 p = 1) : d355 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d1342, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7042 p hg
    simpa only [d1342, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7044 (p : Pattern) (guard : d1343 p = 1) : d356 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d356, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d1343, d356, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d356, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7043 p hg
    simpa only [d1343, d356, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7045 (p : Pattern) (guard : d1316 p = 1) : d56 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1313 p = 1 := by simpa only [d1316, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6345 p hg
    simpa only [d1316, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1315 p = 1 := by simpa only [d1316, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6513 p hg
    simpa only [d1316, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7046 (p : Pattern) (guard : d1318 p = 1) : d56 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d1318, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d1318, d56, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7047 (p : Pattern) (guard : d1319 p = 1) : d56 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7045 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7048 (p : Pattern) (guard : d1322 p = 1) : d56 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7047 p hg
    simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d1322, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7049 (p : Pattern) (guard : d1324 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7050 (p : Pattern) (guard : d1325 p = 1) : d56 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7048 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7049 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7051 (p : Pattern) (guard : d1326 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7052 (p : Pattern) (guard : d1327 p = 1) : d56 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7049 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7053 (p : Pattern) (guard : d1328 p = 1) : d56 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7050 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7054 (p : Pattern) (guard : d1320 p = 1) : d61 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d61, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d1320, d61, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d61, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d1320, d61, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7055 (p : Pattern) (guard : d1321 p = 1) : d62 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d1321, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7054 p hg
    simpa only [d1321, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7056 (p : Pattern) (guard : d1324 p = 1) : d62 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7055 p hg
    simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d1324, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7057 (p : Pattern) (guard : d1326 p = 1) : d62 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7058 (p : Pattern) (guard : d1327 p = 1) : d62 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7056 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7057 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7059 (p : Pattern) (guard : d1329 p = 1) : d62 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7057 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7060 (p : Pattern) (guard : d1330 p = 1) : d62 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7061 (p : Pattern) (guard : d1331 p = 1) : d451 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7053 p hg
    simpa only [d1331, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7060 p hg
    simpa only [d1331, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7062 (p : Pattern) (guard : d1324 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d1324, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1324, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7063 (p : Pattern) (guard : d1326 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1326, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1326, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7064 (p : Pattern) (guard : d1327 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7062 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7063 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7065 (p : Pattern) (guard : d0 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7066 (p : Pattern) (guard : d1329 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7063 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7065 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7067 (p : Pattern) (guard : d1330 p = 1) : d452 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7064 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7066 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7068 (p : Pattern) (guard : d1326 p = 1) : d453 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d1326, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1326, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7069 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7070 (p : Pattern) (guard : d1329 p = 1) : d453 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7068 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7069 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7071 (p : Pattern) (guard : d1332 p = 1) : d453 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7070 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7069 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7072 (p : Pattern) (guard : d1333 p = 1) : d454 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7067 p hg
    simpa only [d1333, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7071 p hg
    simpa only [d1333, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7073 (p : Pattern) (guard : d1334 p = 1) : d455 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d455, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7061 p hg
    simpa only [d1334, d455, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d455, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7072 p hg
    simpa only [d1334, d455, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7074 (p : Pattern) (guard : d1330 p = 1) : d456 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d1330, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7075 (p : Pattern) (guard : d1332 p = 1) : d457 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d1332, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7076 (p : Pattern) (guard : d1333 p = 1) : d458 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7074 p hg
    simpa only [d1333, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d1333, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7077 (p : Pattern) (guard : d1332 p = 1) : d459 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7066 p hg
    simpa only [d1332, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7078 (p : Pattern) (guard : d0 p = 1) : d460 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7079 (p : Pattern) (guard : d1335 p = 1) : d461 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7077 p hg
    simpa only [d1335, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7078 p hg
    simpa only [d1335, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7080 (p : Pattern) (guard : d1336 p = 1) : d462 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7076 p hg
    simpa only [d1336, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7079 p hg
    simpa only [d1336, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7081 (p : Pattern) (guard : d1337 p = 1) : d463 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d463, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7073 p hg
    simpa only [d1337, d463, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d463, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7080 p hg
    simpa only [d1337, d463, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7082 (p : Pattern) (guard : d1339 p = 1) : d464 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7080 p hg
    simpa only [d1339, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7083 (p : Pattern) (guard : d1340 p = 1) : d465 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7081 p hg
    simpa only [d1340, d465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7082 p hg
    simpa only [d1340, d465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7084 (p : Pattern) (guard : d0 p = 1) : d466 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7085 (p : Pattern) (guard : d1329 p = 1) : d467 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d1329, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d1329, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7086 (p : Pattern) (guard : d1330 p = 1) : d468 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d1330, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7085 p hg
    simpa only [d1330, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7087 (p : Pattern) (guard : d0 p = 1) : d470 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7088 (p : Pattern) (guard : d1332 p = 1) : d471 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d1332, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d1332, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7089 (p : Pattern) (guard : d1333 p = 1) : d472 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d1333, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d1333, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7090 (p : Pattern) (guard : d1336 p = 1) : d473 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d1336, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7091 (p : Pattern) (guard : d1326 p = 1) : d466 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d1326, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1326, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7092 (p : Pattern) (guard : d1329 p = 1) : d466 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7093 (p : Pattern) (guard : d1332 p = 1) : d474 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7092 p hg
    simpa only [d1332, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7094 (p : Pattern) (guard : d0 p = 1) : d475 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7095 (p : Pattern) (guard : d1335 p = 1) : d476 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d1335, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1335, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7096 (p : Pattern) (guard : d1338 p = 1) : d477 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7095 p hg
    simpa only [d1338, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7097 (p : Pattern) (guard : d1339 p = 1) : d478 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d1339, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7096 p hg
    simpa only [d1339, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7098 (p : Pattern) (guard : d1332 p = 1) : d479 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7085 p hg
    simpa only [d1332, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7099 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7100 (p : Pattern) (guard : d1335 p = 1) : d481 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1335, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7099 p hg
    simpa only [d1335, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7101 (p : Pattern) (guard : d1338 p = 1) : d482 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7100 p hg
    simpa only [d1338, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7102 (p : Pattern) (guard : d1341 p = 1) : d483 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7101 p hg
    simpa only [d1341, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7103 (p : Pattern) (guard : d1342 p = 1) : d484 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d1342, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7102 p hg
    simpa only [d1342, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7104 (p : Pattern) (guard : d1343 p = 1) : d485 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d485, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7083 p hg
    simpa only [d1343, d485, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d485, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7103 p hg
    simpa only [d1343, d485, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7105 (p : Pattern) (guard : d1330 p = 1) : d106 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7106 (p : Pattern) (guard : d1332 p = 1) : d109 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6408 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7107 (p : Pattern) (guard : d1333 p = 1) : d227 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7105 p hg
    simpa only [d1333, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7106 p hg
    simpa only [d1333, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7108 (p : Pattern) (guard : d1334 p = 1) : d228 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d228, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d1334, d228, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d228, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d1334, d228, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7109 (p : Pattern) (guard : d1332 p = 1) : d229 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d1332, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d1332, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7110 (p : Pattern) (guard : d0 p = 1) : d230 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7111 (p : Pattern) (guard : d1335 p = 1) : d231 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1335, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7110 p hg
    simpa only [d1335, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7112 (p : Pattern) (guard : d1336 p = 1) : d232 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d1336, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d1336, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7113 (p : Pattern) (guard : d1337 p = 1) : d233 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d233, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7108 p hg
    simpa only [d1337, d233, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d233, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7112 p hg
    simpa only [d1337, d233, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7114 (p : Pattern) (guard : d1339 p = 1) : d234 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7112 p hg
    simpa only [d1339, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7115 (p : Pattern) (guard : d1340 p = 1) : d235 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d235, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7113 p hg
    simpa only [d1340, d235, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d235, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7114 p hg
    simpa only [d1340, d235, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7116 (p : Pattern) (guard : d1343 p = 1) : d236 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d236, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7115 p hg
    simpa only [d1343, d236, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d236, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6551 p hg
    simpa only [d1343, d236, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7117 (p : Pattern) (guard : d1312 p = 1) : d15 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1309 p = 1 := by simpa only [d1312, d15, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d1312, d15, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1311 p = 1 := by simpa only [d1312, d15, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d1312, d15, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7118 (p : Pattern) (guard : d1314 p = 1) : d15 p ≤ (0 : Int) + d5 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d1314, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d1314, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7119 (p : Pattern) (guard : d1315 p = 1) : d15 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1312 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1314 p = 1 := by simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d1315, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7120 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7121 (p : Pattern) (guard : d1317 p = 1) : d15 p ≤ (0 : Int) + d5 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7122 (p : Pattern) (guard : d1318 p = 1) : d15 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1315 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7119 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1317 p = 1 := by simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d1318, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7123 (p : Pattern) (guard : d1319 p = 1) : d21 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1316 p = 1 := by simpa only [d1319, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d1319, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1318 p = 1 := by simpa only [d1319, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7122 p hg
    simpa only [d1319, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7124 (p : Pattern) (guard : d0 p = 1) : d260 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7125 (p : Pattern) (guard : d1320 p = 1) : d261 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d1320, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1320, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7126 (p : Pattern) (guard : d1321 p = 1) : d375 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6362 p hg
    simpa only [d1321, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1321, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7127 (p : Pattern) (guard : d1322 p = 1) : d376 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d376, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7123 p hg
    simpa only [d1322, d376, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d376, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1322, d376, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7128 (p : Pattern) (guard : d1320 p = 1) : d15 p ≤ (0 : Int) + d5 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7129 (p : Pattern) (guard : d1321 p = 1) : d21 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6366 p hg
    simpa only [d1321, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7128 p hg
    simpa only [d1321, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7130 (p : Pattern) (guard : d0 p = 1) : d261 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7131 (p : Pattern) (guard : d1323 p = 1) : d375 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d1323, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7130 p hg
    simpa only [d1323, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7132 (p : Pattern) (guard : d1324 p = 1) : d376 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1324, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7131 p hg
    simpa only [d1324, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7133 (p : Pattern) (guard : d1325 p = 1) : d376 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7132 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7134 (p : Pattern) (guard : d1323 p = 1) : d21 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d1323, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d1323, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7135 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7136 (p : Pattern) (guard : d1326 p = 1) : d376 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d1326, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7135 p hg
    simpa only [d1326, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7137 (p : Pattern) (guard : d1327 p = 1) : d376 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7132 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7138 (p : Pattern) (guard : d1328 p = 1) : d376 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7139 (p : Pattern) (guard : d1311 p = 1) : d17 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d1311, d17, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d1311, d17, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1311, d17, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d1311, d17, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
