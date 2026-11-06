/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1320 (p : Pattern) : Int := if p 133 then d71 p else d26 p
theorem agree1320 (p q : Pattern) (h : Agree support p q) : d1320 p = d1320 q := by
  simp only [d1320, h 133 (by decide), agree71 p q h, agree26 p q h]
theorem nonnegative1320 (p : Pattern) : 0 ≤ d1320 p :=
  nonnegative_ite (p 133) (nonnegative71 p) (nonnegative26 p)
def d1321 (p : Pattern) : Int := if p 132 then d1320 p else d1309 p
theorem agree1321 (p q : Pattern) (h : Agree support p q) : d1321 p = d1321 q := by
  simp only [d1321, h 132 (by decide), agree1320 p q h, agree1309 p q h]
theorem nonnegative1321 (p : Pattern) : 0 ≤ d1321 p :=
  nonnegative_ite (p 132) (nonnegative1320 p) (nonnegative1309 p)
def d1322 (p : Pattern) : Int := if p 133 then d70 p else d26 p
theorem agree1322 (p q : Pattern) (h : Agree support p q) : d1322 p = d1322 q := by
  simp only [d1322, h 133 (by decide), agree70 p q h, agree26 p q h]
theorem nonnegative1322 (p : Pattern) : 0 ≤ d1322 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative26 p)
def d1323 (p : Pattern) : Int := if p 132 then d1322 p else d1309 p
theorem agree1323 (p q : Pattern) (h : Agree support p q) : d1323 p = d1323 q := by
  simp only [d1323, h 132 (by decide), agree1322 p q h, agree1309 p q h]
theorem nonnegative1323 (p : Pattern) : 0 ≤ d1323 p :=
  nonnegative_ite (p 132) (nonnegative1322 p) (nonnegative1309 p)
def d1324 (p : Pattern) : Int := if p 113 then d1323 p else d1321 p
theorem agree1324 (p q : Pattern) (h : Agree support p q) : d1324 p = d1324 q := by
  simp only [d1324, h 113 (by decide), agree1323 p q h, agree1321 p q h]
theorem nonnegative1324 (p : Pattern) : 0 ≤ d1324 p :=
  nonnegative_ite (p 113) (nonnegative1323 p) (nonnegative1321 p)
def d1325 (p : Pattern) : Int := if p 133 then d70 p else d25 p
theorem agree1325 (p q : Pattern) (h : Agree support p q) : d1325 p = d1325 q := by
  simp only [d1325, h 133 (by decide), agree70 p q h, agree25 p q h]
theorem nonnegative1325 (p : Pattern) : 0 ≤ d1325 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative25 p)
def d1326 (p : Pattern) : Int := if p 132 then d1325 p else d1312 p
theorem agree1326 (p q : Pattern) (h : Agree support p q) : d1326 p = d1326 q := by
  simp only [d1326, h 132 (by decide), agree1325 p q h, agree1312 p q h]
theorem nonnegative1326 (p : Pattern) : 0 ≤ d1326 p :=
  nonnegative_ite (p 132) (nonnegative1325 p) (nonnegative1312 p)
def d1327 (p : Pattern) : Int := if p 133 then d70 p else d55 p
theorem agree1327 (p q : Pattern) (h : Agree support p q) : d1327 p = d1327 q := by
  simp only [d1327, h 133 (by decide), agree70 p q h, agree55 p q h]
theorem nonnegative1327 (p : Pattern) : 0 ≤ d1327 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative55 p)
def d1328 (p : Pattern) : Int := if p 132 then d1327 p else d1315 p
theorem agree1328 (p q : Pattern) (h : Agree support p q) : d1328 p = d1328 q := by
  simp only [d1328, h 132 (by decide), agree1327 p q h, agree1315 p q h]
theorem nonnegative1328 (p : Pattern) : 0 ≤ d1328 p :=
  nonnegative_ite (p 132) (nonnegative1327 p) (nonnegative1315 p)
def d1329 (p : Pattern) : Int := if p 113 then d1328 p else d1326 p
theorem agree1329 (p q : Pattern) (h : Agree support p q) : d1329 p = d1329 q := by
  simp only [d1329, h 113 (by decide), agree1328 p q h, agree1326 p q h]
theorem nonnegative1329 (p : Pattern) : 0 ≤ d1329 p :=
  nonnegative_ite (p 113) (nonnegative1328 p) (nonnegative1326 p)
def d1330 (p : Pattern) : Int := if p 112 then d1329 p else d1324 p
theorem agree1330 (p q : Pattern) (h : Agree support p q) : d1330 p = d1330 q := by
  simp only [d1330, h 112 (by decide), agree1329 p q h, agree1324 p q h]
theorem nonnegative1330 (p : Pattern) : 0 ≤ d1330 p :=
  nonnegative_ite (p 112) (nonnegative1329 p) (nonnegative1324 p)
def d1331 (p : Pattern) : Int := if p 106 then d1330 p else d1319 p
theorem agree1331 (p q : Pattern) (h : Agree support p q) : d1331 p = d1331 q := by
  simp only [d1331, h 106 (by decide), agree1330 p q h, agree1319 p q h]
theorem nonnegative1331 (p : Pattern) : 0 ≤ d1331 p :=
  nonnegative_ite (p 106) (nonnegative1330 p) (nonnegative1319 p)
def d1332 (p : Pattern) : Int := if p 133 then d87 p else d86 p
theorem agree1332 (p q : Pattern) (h : Agree support p q) : d1332 p = d1332 q := by
  simp only [d1332, h 133 (by decide), agree87 p q h, agree86 p q h]
theorem nonnegative1332 (p : Pattern) : 0 ≤ d1332 p :=
  nonnegative_ite (p 133) (nonnegative87 p) (nonnegative86 p)
def d1333 (p : Pattern) : Int := if p 133 then d87 p else d90 p
theorem agree1333 (p q : Pattern) (h : Agree support p q) : d1333 p = d1333 q := by
  simp only [d1333, h 133 (by decide), agree87 p q h, agree90 p q h]
theorem nonnegative1333 (p : Pattern) : 0 ≤ d1333 p :=
  nonnegative_ite (p 133) (nonnegative87 p) (nonnegative90 p)
def d1334 (p : Pattern) : Int := if p 132 then d1333 p else d1332 p
theorem agree1334 (p q : Pattern) (h : Agree support p q) : d1334 p = d1334 q := by
  simp only [d1334, h 132 (by decide), agree1333 p q h, agree1332 p q h]
theorem nonnegative1334 (p : Pattern) : 0 ≤ d1334 p :=
  nonnegative_ite (p 132) (nonnegative1333 p) (nonnegative1332 p)
def d1335 (p : Pattern) : Int := if p 113 then d1334 p else d1311 p
theorem agree1335 (p q : Pattern) (h : Agree support p q) : d1335 p = d1335 q := by
  simp only [d1335, h 113 (by decide), agree1334 p q h, agree1311 p q h]
theorem nonnegative1335 (p : Pattern) : 0 ≤ d1335 p :=
  nonnegative_ite (p 113) (nonnegative1334 p) (nonnegative1311 p)
def d1336 (p : Pattern) : Int := if p 133 then d71 p else d98 p
theorem agree1336 (p q : Pattern) (h : Agree support p q) : d1336 p = d1336 q := by
  simp only [d1336, h 133 (by decide), agree71 p q h, agree98 p q h]
theorem nonnegative1336 (p : Pattern) : 0 ≤ d1336 p :=
  nonnegative_ite (p 133) (nonnegative71 p) (nonnegative98 p)
def d1337 (p : Pattern) : Int := if p 132 then d71 p else d1336 p
theorem agree1337 (p q : Pattern) (h : Agree support p q) : d1337 p = d1337 q := by
  simp only [d1337, h 132 (by decide), agree71 p q h, agree1336 p q h]
theorem nonnegative1337 (p : Pattern) : 0 ≤ d1337 p :=
  nonnegative_ite (p 132) (nonnegative71 p) (nonnegative1336 p)
def d1338 (p : Pattern) : Int := if p 112 then d1337 p else d1335 p
theorem agree1338 (p q : Pattern) (h : Agree support p q) : d1338 p = d1338 q := by
  simp only [d1338, h 112 (by decide), agree1337 p q h, agree1335 p q h]
theorem nonnegative1338 (p : Pattern) : 0 ≤ d1338 p :=
  nonnegative_ite (p 112) (nonnegative1337 p) (nonnegative1335 p)
def d1339 (p : Pattern) : Int := if p 133 then d70 p else d87 p
theorem agree1339 (p q : Pattern) (h : Agree support p q) : d1339 p = d1339 q := by
  simp only [d1339, h 133 (by decide), agree70 p q h, agree87 p q h]
theorem nonnegative1339 (p : Pattern) : 0 ≤ d1339 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative87 p)
def d1340 (p : Pattern) : Int := if p 132 then d1339 p else d1332 p
theorem agree1340 (p q : Pattern) (h : Agree support p q) : d1340 p = d1340 q := by
  simp only [d1340, h 132 (by decide), agree1339 p q h, agree1332 p q h]
theorem nonnegative1340 (p : Pattern) : 0 ≤ d1340 p :=
  nonnegative_ite (p 132) (nonnegative1339 p) (nonnegative1332 p)
def d1341 (p : Pattern) : Int := if p 113 then d1340 p else d1323 p
theorem agree1341 (p q : Pattern) (h : Agree support p q) : d1341 p = d1341 q := by
  simp only [d1341, h 113 (by decide), agree1340 p q h, agree1323 p q h]
theorem nonnegative1341 (p : Pattern) : 0 ≤ d1341 p :=
  nonnegative_ite (p 113) (nonnegative1340 p) (nonnegative1323 p)
def d1342 (p : Pattern) : Int := if p 133 then d2 p else d71 p
theorem agree1342 (p q : Pattern) (h : Agree support p q) : d1342 p = d1342 q := by
  simp only [d1342, h 133 (by decide), agree2 p q h, agree71 p q h]
theorem nonnegative1342 (p : Pattern) : 0 ≤ d1342 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative71 p)
def d1343 (p : Pattern) : Int := if p 132 then d1342 p else d1336 p
theorem agree1343 (p q : Pattern) (h : Agree support p q) : d1343 p = d1343 q := by
  simp only [d1343, h 132 (by decide), agree1342 p q h, agree1336 p q h]
theorem nonnegative1343 (p : Pattern) : 0 ≤ d1343 p :=
  nonnegative_ite (p 132) (nonnegative1342 p) (nonnegative1336 p)
def d1344 (p : Pattern) : Int := if p 133 then d70 p else d97 p
theorem agree1344 (p q : Pattern) (h : Agree support p q) : d1344 p = d1344 q := by
  simp only [d1344, h 133 (by decide), agree70 p q h, agree97 p q h]
theorem nonnegative1344 (p : Pattern) : 0 ≤ d1344 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative97 p)
def d1345 (p : Pattern) : Int := if p 133 then d2 p else d70 p
theorem agree1345 (p q : Pattern) (h : Agree support p q) : d1345 p = d1345 q := by
  simp only [d1345, h 133 (by decide), agree2 p q h, agree70 p q h]
theorem nonnegative1345 (p : Pattern) : 0 ≤ d1345 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative70 p)
def d1346 (p : Pattern) : Int := if p 132 then d1345 p else d1344 p
theorem agree1346 (p q : Pattern) (h : Agree support p q) : d1346 p = d1346 q := by
  simp only [d1346, h 132 (by decide), agree1345 p q h, agree1344 p q h]
theorem nonnegative1346 (p : Pattern) : 0 ≤ d1346 p :=
  nonnegative_ite (p 132) (nonnegative1345 p) (nonnegative1344 p)
def d1347 (p : Pattern) : Int := if p 113 then d1346 p else d1343 p
theorem agree1347 (p q : Pattern) (h : Agree support p q) : d1347 p = d1347 q := by
  simp only [d1347, h 113 (by decide), agree1346 p q h, agree1343 p q h]
theorem nonnegative1347 (p : Pattern) : 0 ≤ d1347 p :=
  nonnegative_ite (p 113) (nonnegative1346 p) (nonnegative1343 p)
def d1348 (p : Pattern) : Int := if p 112 then d1347 p else d1341 p
theorem agree1348 (p q : Pattern) (h : Agree support p q) : d1348 p = d1348 q := by
  simp only [d1348, h 112 (by decide), agree1347 p q h, agree1341 p q h]
theorem nonnegative1348 (p : Pattern) : 0 ≤ d1348 p :=
  nonnegative_ite (p 112) (nonnegative1347 p) (nonnegative1341 p)
def d1349 (p : Pattern) : Int := if p 106 then d1348 p else d1338 p
theorem agree1349 (p q : Pattern) (h : Agree support p q) : d1349 p = d1349 q := by
  simp only [d1349, h 106 (by decide), agree1348 p q h, agree1338 p q h]
theorem nonnegative1349 (p : Pattern) : 0 ≤ d1349 p :=
  nonnegative_ite (p 106) (nonnegative1348 p) (nonnegative1338 p)
def d1350 (p : Pattern) : Int := if p 86 then d1349 p else d1331 p
theorem agree1350 (p q : Pattern) (h : Agree support p q) : d1350 p = d1350 q := by
  simp only [d1350, h 86 (by decide), agree1349 p q h, agree1331 p q h]
theorem nonnegative1350 (p : Pattern) : 0 ≤ d1350 p :=
  nonnegative_ite (p 86) (nonnegative1349 p) (nonnegative1331 p)
def d1351 (p : Pattern) : Int := if p 112 then d1329 p else d1323 p
theorem agree1351 (p q : Pattern) (h : Agree support p q) : d1351 p = d1351 q := by
  simp only [d1351, h 112 (by decide), agree1329 p q h, agree1323 p q h]
theorem nonnegative1351 (p : Pattern) : 0 ≤ d1351 p :=
  nonnegative_ite (p 112) (nonnegative1329 p) (nonnegative1323 p)
def d1352 (p : Pattern) : Int := if p 106 then d1351 p else d1319 p
theorem agree1352 (p q : Pattern) (h : Agree support p q) : d1352 p = d1352 q := by
  simp only [d1352, h 106 (by decide), agree1351 p q h, agree1319 p q h]
theorem nonnegative1352 (p : Pattern) : 0 ≤ d1352 p :=
  nonnegative_ite (p 106) (nonnegative1351 p) (nonnegative1319 p)
def d1353 (p : Pattern) : Int := if p 133 then d87 p else d120 p
theorem agree1353 (p q : Pattern) (h : Agree support p q) : d1353 p = d1353 q := by
  simp only [d1353, h 133 (by decide), agree87 p q h, agree120 p q h]
theorem nonnegative1353 (p : Pattern) : 0 ≤ d1353 p :=
  nonnegative_ite (p 133) (nonnegative87 p) (nonnegative120 p)
def d1354 (p : Pattern) : Int := if p 132 then d1353 p else d1332 p
theorem agree1354 (p q : Pattern) (h : Agree support p q) : d1354 p = d1354 q := by
  simp only [d1354, h 132 (by decide), agree1353 p q h, agree1332 p q h]
theorem nonnegative1354 (p : Pattern) : 0 ≤ d1354 p :=
  nonnegative_ite (p 132) (nonnegative1353 p) (nonnegative1332 p)
def d1355 (p : Pattern) : Int := if p 113 then d1354 p else d1311 p
theorem agree1355 (p q : Pattern) (h : Agree support p q) : d1355 p = d1355 q := by
  simp only [d1355, h 113 (by decide), agree1354 p q h, agree1311 p q h]
theorem nonnegative1355 (p : Pattern) : 0 ≤ d1355 p :=
  nonnegative_ite (p 113) (nonnegative1354 p) (nonnegative1311 p)
def d1356 (p : Pattern) : Int := if p 132 then d70 p else d1344 p
theorem agree1356 (p q : Pattern) (h : Agree support p q) : d1356 p = d1356 q := by
  simp only [d1356, h 132 (by decide), agree70 p q h, agree1344 p q h]
theorem nonnegative1356 (p : Pattern) : 0 ≤ d1356 p :=
  nonnegative_ite (p 132) (nonnegative70 p) (nonnegative1344 p)
def d1357 (p : Pattern) : Int := if p 113 then d1356 p else d1337 p
theorem agree1357 (p q : Pattern) (h : Agree support p q) : d1357 p = d1357 q := by
  simp only [d1357, h 113 (by decide), agree1356 p q h, agree1337 p q h]
theorem nonnegative1357 (p : Pattern) : 0 ≤ d1357 p :=
  nonnegative_ite (p 113) (nonnegative1356 p) (nonnegative1337 p)
def d1358 (p : Pattern) : Int := if p 112 then d1357 p else d1355 p
theorem agree1358 (p q : Pattern) (h : Agree support p q) : d1358 p = d1358 q := by
  simp only [d1358, h 112 (by decide), agree1357 p q h, agree1355 p q h]
theorem nonnegative1358 (p : Pattern) : 0 ≤ d1358 p :=
  nonnegative_ite (p 112) (nonnegative1357 p) (nonnegative1355 p)
def d1359 (p : Pattern) : Int := if p 113 then d1328 p else d1323 p
theorem agree1359 (p q : Pattern) (h : Agree support p q) : d1359 p = d1359 q := by
  simp only [d1359, h 113 (by decide), agree1328 p q h, agree1323 p q h]
theorem nonnegative1359 (p : Pattern) : 0 ≤ d1359 p :=
  nonnegative_ite (p 113) (nonnegative1328 p) (nonnegative1323 p)
def d1360 (p : Pattern) : Int := if p 113 then d2 p else d1346 p
theorem agree1360 (p q : Pattern) (h : Agree support p q) : d1360 p = d1360 q := by
  simp only [d1360, h 113 (by decide), agree2 p q h, agree1346 p q h]
theorem nonnegative1360 (p : Pattern) : 0 ≤ d1360 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1346 p)
def d1361 (p : Pattern) : Int := if p 112 then d1360 p else d1359 p
theorem agree1361 (p q : Pattern) (h : Agree support p q) : d1361 p = d1361 q := by
  simp only [d1361, h 112 (by decide), agree1360 p q h, agree1359 p q h]
theorem nonnegative1361 (p : Pattern) : 0 ≤ d1361 p :=
  nonnegative_ite (p 112) (nonnegative1360 p) (nonnegative1359 p)
def d1362 (p : Pattern) : Int := if p 106 then d1361 p else d1358 p
theorem agree1362 (p q : Pattern) (h : Agree support p q) : d1362 p = d1362 q := by
  simp only [d1362, h 106 (by decide), agree1361 p q h, agree1358 p q h]
theorem nonnegative1362 (p : Pattern) : 0 ≤ d1362 p :=
  nonnegative_ite (p 106) (nonnegative1361 p) (nonnegative1358 p)
def d1363 (p : Pattern) : Int := if p 86 then d1362 p else d1352 p
theorem agree1363 (p q : Pattern) (h : Agree support p q) : d1363 p = d1363 q := by
  simp only [d1363, h 86 (by decide), agree1362 p q h, agree1352 p q h]
theorem nonnegative1363 (p : Pattern) : 0 ≤ d1363 p :=
  nonnegative_ite (p 86) (nonnegative1362 p) (nonnegative1352 p)
def d1364 (p : Pattern) : Int := if p 80 then d1363 p else d1350 p
theorem agree1364 (p q : Pattern) (h : Agree support p q) : d1364 p = d1364 q := by
  simp only [d1364, h 80 (by decide), agree1363 p q h, agree1350 p q h]
theorem nonnegative1364 (p : Pattern) : 0 ≤ d1364 p :=
  nonnegative_ite (p 80) (nonnegative1363 p) (nonnegative1350 p)
def d1365 (p : Pattern) : Int := if p 138 then d1088 p else d0 p
theorem agree1365 (p q : Pattern) (h : Agree support p q) : d1365 p = d1365 q := by
  simp only [d1365, h 138 (by decide), agree1088 p q h, agree0 p q h]
theorem nonnegative1365 (p : Pattern) : 0 ≤ d1365 p :=
  nonnegative_ite (p 138) (nonnegative1088 p) (nonnegative0 p)
def d1366 (p : Pattern) : Int := if p 133 then d2 p else d1097 p
theorem agree1366 (p q : Pattern) (h : Agree support p q) : d1366 p = d1366 q := by
  simp only [d1366, h 133 (by decide), agree2 p q h, agree1097 p q h]
theorem nonnegative1366 (p : Pattern) : 0 ≤ d1366 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1097 p)
def d1367 (p : Pattern) : Int := if p 132 then d1366 p else d1098 p
theorem agree1367 (p q : Pattern) (h : Agree support p q) : d1367 p = d1367 q := by
  simp only [d1367, h 132 (by decide), agree1366 p q h, agree1098 p q h]
theorem nonnegative1367 (p : Pattern) : 0 ≤ d1367 p :=
  nonnegative_ite (p 132) (nonnegative1366 p) (nonnegative1098 p)
def d1368 (p : Pattern) : Int := if p 113 then d1367 p else d1105 p
theorem agree1368 (p q : Pattern) (h : Agree support p q) : d1368 p = d1368 q := by
  simp only [d1368, h 113 (by decide), agree1367 p q h, agree1105 p q h]
theorem nonnegative1368 (p : Pattern) : 0 ≤ d1368 p :=
  nonnegative_ite (p 113) (nonnegative1367 p) (nonnegative1105 p)
def d1369 (p : Pattern) : Int := if p 112 then d1113 p else d1368 p
theorem agree1369 (p q : Pattern) (h : Agree support p q) : d1369 p = d1369 q := by
  simp only [d1369, h 112 (by decide), agree1113 p q h, agree1368 p q h]
theorem nonnegative1369 (p : Pattern) : 0 ≤ d1369 p :=
  nonnegative_ite (p 112) (nonnegative1113 p) (nonnegative1368 p)
def d1370 (p : Pattern) : Int := if p 106 then d1369 p else d1111 p
theorem agree1370 (p q : Pattern) (h : Agree support p q) : d1370 p = d1370 q := by
  simp only [d1370, h 106 (by decide), agree1369 p q h, agree1111 p q h]
theorem nonnegative1370 (p : Pattern) : 0 ≤ d1370 p :=
  nonnegative_ite (p 106) (nonnegative1369 p) (nonnegative1111 p)
def d1371 (p : Pattern) : Int := if p 112 then d1117 p else d1367 p
theorem agree1371 (p q : Pattern) (h : Agree support p q) : d1371 p = d1371 q := by
  simp only [d1371, h 112 (by decide), agree1117 p q h, agree1367 p q h]
theorem nonnegative1371 (p : Pattern) : 0 ≤ d1371 p :=
  nonnegative_ite (p 112) (nonnegative1117 p) (nonnegative1367 p)
def d1372 (p : Pattern) : Int := if p 106 then d1371 p else d1111 p
theorem agree1372 (p q : Pattern) (h : Agree support p q) : d1372 p = d1372 q := by
  simp only [d1372, h 106 (by decide), agree1371 p q h, agree1111 p q h]
theorem nonnegative1372 (p : Pattern) : 0 ≤ d1372 p :=
  nonnegative_ite (p 106) (nonnegative1371 p) (nonnegative1111 p)
def d1373 (p : Pattern) : Int := if p 86 then d1372 p else d1370 p
theorem agree1373 (p q : Pattern) (h : Agree support p q) : d1373 p = d1373 q := by
  simp only [d1373, h 86 (by decide), agree1372 p q h, agree1370 p q h]
theorem nonnegative1373 (p : Pattern) : 0 ≤ d1373 p :=
  nonnegative_ite (p 86) (nonnegative1372 p) (nonnegative1370 p)
def d1374 (p : Pattern) : Int := if p 112 then d1113 p else d1367 p
theorem agree1374 (p q : Pattern) (h : Agree support p q) : d1374 p = d1374 q := by
  simp only [d1374, h 112 (by decide), agree1113 p q h, agree1367 p q h]
theorem nonnegative1374 (p : Pattern) : 0 ≤ d1374 p :=
  nonnegative_ite (p 112) (nonnegative1113 p) (nonnegative1367 p)
def d1375 (p : Pattern) : Int := if p 106 then d1374 p else d1111 p
theorem agree1375 (p q : Pattern) (h : Agree support p q) : d1375 p = d1375 q := by
  simp only [d1375, h 106 (by decide), agree1374 p q h, agree1111 p q h]
theorem nonnegative1375 (p : Pattern) : 0 ≤ d1375 p :=
  nonnegative_ite (p 106) (nonnegative1374 p) (nonnegative1111 p)
def d1376 (p : Pattern) : Int := if p 133 then d1100 p else d1097 p
theorem agree1376 (p q : Pattern) (h : Agree support p q) : d1376 p = d1376 q := by
  simp only [d1376, h 133 (by decide), agree1100 p q h, agree1097 p q h]
theorem nonnegative1376 (p : Pattern) : 0 ≤ d1376 p :=
  nonnegative_ite (p 133) (nonnegative1100 p) (nonnegative1097 p)
def d1377 (p : Pattern) : Int := if p 132 then d1376 p else d1098 p
theorem agree1377 (p q : Pattern) (h : Agree support p q) : d1377 p = d1377 q := by
  simp only [d1377, h 132 (by decide), agree1376 p q h, agree1098 p q h]
theorem nonnegative1377 (p : Pattern) : 0 ≤ d1377 p :=
  nonnegative_ite (p 132) (nonnegative1376 p) (nonnegative1098 p)
def d1378 (p : Pattern) : Int := if p 113 then d1377 p else d1102 p
theorem agree1378 (p q : Pattern) (h : Agree support p q) : d1378 p = d1378 q := by
  simp only [d1378, h 113 (by decide), agree1377 p q h, agree1102 p q h]
theorem nonnegative1378 (p : Pattern) : 0 ≤ d1378 p :=
  nonnegative_ite (p 113) (nonnegative1377 p) (nonnegative1102 p)
def d1379 (p : Pattern) : Int := if p 113 then d2 p else d1110 p
theorem agree1379 (p q : Pattern) (h : Agree support p q) : d1379 p = d1379 q := by
  simp only [d1379, h 113 (by decide), agree2 p q h, agree1110 p q h]
theorem nonnegative1379 (p : Pattern) : 0 ≤ d1379 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1110 p)
def d1380 (p : Pattern) : Int := if p 112 then d1379 p else d1378 p
theorem agree1380 (p q : Pattern) (h : Agree support p q) : d1380 p = d1380 q := by
  simp only [d1380, h 112 (by decide), agree1379 p q h, agree1378 p q h]
theorem nonnegative1380 (p : Pattern) : 0 ≤ d1380 p :=
  nonnegative_ite (p 112) (nonnegative1379 p) (nonnegative1378 p)
def d1381 (p : Pattern) : Int := if p 113 then d1113 p else d1367 p
theorem agree1381 (p q : Pattern) (h : Agree support p q) : d1381 p = d1381 q := by
  simp only [d1381, h 113 (by decide), agree1113 p q h, agree1367 p q h]
theorem nonnegative1381 (p : Pattern) : 0 ≤ d1381 p :=
  nonnegative_ite (p 113) (nonnegative1113 p) (nonnegative1367 p)
def d1382 (p : Pattern) : Int := if p 112 then d2 p else d1381 p
theorem agree1382 (p q : Pattern) (h : Agree support p q) : d1382 p = d1382 q := by
  simp only [d1382, h 112 (by decide), agree2 p q h, agree1381 p q h]
theorem nonnegative1382 (p : Pattern) : 0 ≤ d1382 p :=
  nonnegative_ite (p 112) (nonnegative2 p) (nonnegative1381 p)
def d1383 (p : Pattern) : Int := if p 106 then d1382 p else d1380 p
theorem agree1383 (p q : Pattern) (h : Agree support p q) : d1383 p = d1383 q := by
  simp only [d1383, h 106 (by decide), agree1382 p q h, agree1380 p q h]
theorem nonnegative1383 (p : Pattern) : 0 ≤ d1383 p :=
  nonnegative_ite (p 106) (nonnegative1382 p) (nonnegative1380 p)
def d1384 (p : Pattern) : Int := if p 86 then d1383 p else d1375 p
theorem agree1384 (p q : Pattern) (h : Agree support p q) : d1384 p = d1384 q := by
  simp only [d1384, h 86 (by decide), agree1383 p q h, agree1375 p q h]
theorem nonnegative1384 (p : Pattern) : 0 ≤ d1384 p :=
  nonnegative_ite (p 86) (nonnegative1383 p) (nonnegative1375 p)
def d1385 (p : Pattern) : Int := if p 80 then d1384 p else d1373 p
theorem agree1385 (p q : Pattern) (h : Agree support p q) : d1385 p = d1385 q := by
  simp only [d1385, h 80 (by decide), agree1384 p q h, agree1373 p q h]
theorem nonnegative1385 (p : Pattern) : 0 ≤ d1385 p :=
  nonnegative_ite (p 80) (nonnegative1384 p) (nonnegative1373 p)
def d1386 (p : Pattern) : Int := if p 106 then d204 p else d197 p
theorem agree1386 (p q : Pattern) (h : Agree support p q) : d1386 p = d1386 q := by
  simp only [d1386, h 106 (by decide), agree204 p q h, agree197 p q h]
theorem nonnegative1386 (p : Pattern) : 0 ≤ d1386 p :=
  nonnegative_ite (p 106) (nonnegative204 p) (nonnegative197 p)
def d1387 (p : Pattern) : Int := if p 106 then d223 p else d215 p
theorem agree1387 (p q : Pattern) (h : Agree support p q) : d1387 p = d1387 q := by
  simp only [d1387, h 106 (by decide), agree223 p q h, agree215 p q h]
theorem nonnegative1387 (p : Pattern) : 0 ≤ d1387 p :=
  nonnegative_ite (p 106) (nonnegative223 p) (nonnegative215 p)
def d1388 (p : Pattern) : Int := if p 80 then d1387 p else d1386 p
theorem agree1388 (p q : Pattern) (h : Agree support p q) : d1388 p = d1388 q := by
  simp only [d1388, h 80 (by decide), agree1387 p q h, agree1386 p q h]
theorem nonnegative1388 (p : Pattern) : 0 ≤ d1388 p :=
  nonnegative_ite (p 80) (nonnegative1387 p) (nonnegative1386 p)
def d1389 (p : Pattern) : Int := if p 112 then d51 p else d1102 p
theorem agree1389 (p q : Pattern) (h : Agree support p q) : d1389 p = d1389 q := by
  simp only [d1389, h 112 (by decide), agree51 p q h, agree1102 p q h]
theorem nonnegative1389 (p : Pattern) : 0 ≤ d1389 p :=
  nonnegative_ite (p 112) (nonnegative51 p) (nonnegative1102 p)
def d1390 (p : Pattern) : Int := if p 133 then d75 p else d1097 p
theorem agree1390 (p q : Pattern) (h : Agree support p q) : d1390 p = d1390 q := by
  simp only [d1390, h 133 (by decide), agree75 p q h, agree1097 p q h]
theorem nonnegative1390 (p : Pattern) : 0 ≤ d1390 p :=
  nonnegative_ite (p 133) (nonnegative75 p) (nonnegative1097 p)
def d1391 (p : Pattern) : Int := if p 132 then d1390 p else d1098 p
theorem agree1391 (p q : Pattern) (h : Agree support p q) : d1391 p = d1391 q := by
  simp only [d1391, h 132 (by decide), agree1390 p q h, agree1098 p q h]
theorem nonnegative1391 (p : Pattern) : 0 ≤ d1391 p :=
  nonnegative_ite (p 132) (nonnegative1390 p) (nonnegative1098 p)
def d1392 (p : Pattern) : Int := if p 113 then d1391 p else d1105 p
theorem agree1392 (p q : Pattern) (h : Agree support p q) : d1392 p = d1392 q := by
  simp only [d1392, h 113 (by decide), agree1391 p q h, agree1105 p q h]
theorem nonnegative1392 (p : Pattern) : 0 ≤ d1392 p :=
  nonnegative_ite (p 113) (nonnegative1391 p) (nonnegative1105 p)
def d1393 (p : Pattern) : Int := if p 112 then d80 p else d1392 p
theorem agree1393 (p q : Pattern) (h : Agree support p q) : d1393 p = d1393 q := by
  simp only [d1393, h 112 (by decide), agree80 p q h, agree1392 p q h]
theorem nonnegative1393 (p : Pattern) : 0 ≤ d1393 p :=
  nonnegative_ite (p 112) (nonnegative80 p) (nonnegative1392 p)
def d1394 (p : Pattern) : Int := if p 106 then d1393 p else d1389 p
theorem agree1394 (p q : Pattern) (h : Agree support p q) : d1394 p = d1394 q := by
  simp only [d1394, h 106 (by decide), agree1393 p q h, agree1389 p q h]
theorem nonnegative1394 (p : Pattern) : 0 ≤ d1394 p :=
  nonnegative_ite (p 106) (nonnegative1393 p) (nonnegative1389 p)
def d1395 (p : Pattern) : Int := if p 113 then d112 p else d1113 p
theorem agree1395 (p q : Pattern) (h : Agree support p q) : d1395 p = d1395 q := by
  simp only [d1395, h 113 (by decide), agree112 p q h, agree1113 p q h]
theorem nonnegative1395 (p : Pattern) : 0 ≤ d1395 p :=
  nonnegative_ite (p 113) (nonnegative112 p) (nonnegative1113 p)
def d1396 (p : Pattern) : Int := if p 112 then d1395 p else d1391 p
theorem agree1396 (p q : Pattern) (h : Agree support p q) : d1396 p = d1396 q := by
  simp only [d1396, h 112 (by decide), agree1395 p q h, agree1391 p q h]
theorem nonnegative1396 (p : Pattern) : 0 ≤ d1396 p :=
  nonnegative_ite (p 112) (nonnegative1395 p) (nonnegative1391 p)
def d1397 (p : Pattern) : Int := if p 106 then d1396 p else d1111 p
theorem agree1397 (p q : Pattern) (h : Agree support p q) : d1397 p = d1397 q := by
  simp only [d1397, h 106 (by decide), agree1396 p q h, agree1111 p q h]
theorem nonnegative1397 (p : Pattern) : 0 ≤ d1397 p :=
  nonnegative_ite (p 106) (nonnegative1396 p) (nonnegative1111 p)
def d1398 (p : Pattern) : Int := if p 86 then d1397 p else d1394 p
theorem agree1398 (p q : Pattern) (h : Agree support p q) : d1398 p = d1398 q := by
  simp only [d1398, h 86 (by decide), agree1397 p q h, agree1394 p q h]
theorem nonnegative1398 (p : Pattern) : 0 ≤ d1398 p :=
  nonnegative_ite (p 86) (nonnegative1397 p) (nonnegative1394 p)
def d1399 (p : Pattern) : Int := if p 112 then d80 p else d1391 p
theorem agree1399 (p q : Pattern) (h : Agree support p q) : d1399 p = d1399 q := by
  simp only [d1399, h 112 (by decide), agree80 p q h, agree1391 p q h]
theorem nonnegative1399 (p : Pattern) : 0 ≤ d1399 p :=
  nonnegative_ite (p 112) (nonnegative80 p) (nonnegative1391 p)
def d1400 (p : Pattern) : Int := if p 106 then d1399 p else d1389 p
theorem agree1400 (p q : Pattern) (h : Agree support p q) : d1400 p = d1400 q := by
  simp only [d1400, h 106 (by decide), agree1399 p q h, agree1389 p q h]
theorem nonnegative1400 (p : Pattern) : 0 ≤ d1400 p :=
  nonnegative_ite (p 106) (nonnegative1399 p) (nonnegative1389 p)
def d1401 (p : Pattern) : Int := if p 134 then d119 p else d8 p
theorem agree1401 (p q : Pattern) (h : Agree support p q) : d1401 p = d1401 q := by
  simp only [d1401, h 134 (by decide), agree119 p q h, agree8 p q h]
theorem nonnegative1401 (p : Pattern) : 0 ≤ d1401 p :=
  nonnegative_ite (p 134) (nonnegative119 p) (nonnegative8 p)
def d1402 (p : Pattern) : Int := if p 133 then d1100 p else d1401 p
theorem agree1402 (p q : Pattern) (h : Agree support p q) : d1402 p = d1402 q := by
  simp only [d1402, h 133 (by decide), agree1100 p q h, agree1401 p q h]
theorem nonnegative1402 (p : Pattern) : 0 ≤ d1402 p :=
  nonnegative_ite (p 133) (nonnegative1100 p) (nonnegative1401 p)
def d1403 (p : Pattern) : Int := if p 132 then d1402 p else d1098 p
theorem agree1403 (p q : Pattern) (h : Agree support p q) : d1403 p = d1403 q := by
  simp only [d1403, h 132 (by decide), agree1402 p q h, agree1098 p q h]
theorem nonnegative1403 (p : Pattern) : 0 ≤ d1403 p :=
  nonnegative_ite (p 132) (nonnegative1402 p) (nonnegative1098 p)
def d1404 (p : Pattern) : Int := if p 113 then d1403 p else d1102 p
theorem agree1404 (p q : Pattern) (h : Agree support p q) : d1404 p = d1404 q := by
  simp only [d1404, h 113 (by decide), agree1403 p q h, agree1102 p q h]
theorem nonnegative1404 (p : Pattern) : 0 ≤ d1404 p :=
  nonnegative_ite (p 113) (nonnegative1403 p) (nonnegative1102 p)
def d1405 (p : Pattern) : Int := if p 113 then d126 p else d1110 p
theorem agree1405 (p q : Pattern) (h : Agree support p q) : d1405 p = d1405 q := by
  simp only [d1405, h 113 (by decide), agree126 p q h, agree1110 p q h]
theorem nonnegative1405 (p : Pattern) : 0 ≤ d1405 p :=
  nonnegative_ite (p 113) (nonnegative126 p) (nonnegative1110 p)
def d1406 (p : Pattern) : Int := if p 112 then d1405 p else d1404 p
theorem agree1406 (p q : Pattern) (h : Agree support p q) : d1406 p = d1406 q := by
  simp only [d1406, h 112 (by decide), agree1405 p q h, agree1404 p q h]
theorem nonnegative1406 (p : Pattern) : 0 ≤ d1406 p :=
  nonnegative_ite (p 112) (nonnegative1405 p) (nonnegative1404 p)
def d1407 (p : Pattern) : Int := if p 113 then d80 p else d1391 p
theorem agree1407 (p q : Pattern) (h : Agree support p q) : d1407 p = d1407 q := by
  simp only [d1407, h 113 (by decide), agree80 p q h, agree1391 p q h]
theorem nonnegative1407 (p : Pattern) : 0 ≤ d1407 p :=
  nonnegative_ite (p 113) (nonnegative80 p) (nonnegative1391 p)
def d1408 (p : Pattern) : Int := if p 112 then d130 p else d1407 p
theorem agree1408 (p q : Pattern) (h : Agree support p q) : d1408 p = d1408 q := by
  simp only [d1408, h 112 (by decide), agree130 p q h, agree1407 p q h]
theorem nonnegative1408 (p : Pattern) : 0 ≤ d1408 p :=
  nonnegative_ite (p 112) (nonnegative130 p) (nonnegative1407 p)
def d1409 (p : Pattern) : Int := if p 106 then d1408 p else d1406 p
theorem agree1409 (p q : Pattern) (h : Agree support p q) : d1409 p = d1409 q := by
  simp only [d1409, h 106 (by decide), agree1408 p q h, agree1406 p q h]
theorem nonnegative1409 (p : Pattern) : 0 ≤ d1409 p :=
  nonnegative_ite (p 106) (nonnegative1408 p) (nonnegative1406 p)
def d1410 (p : Pattern) : Int := if p 86 then d1409 p else d1400 p
theorem agree1410 (p q : Pattern) (h : Agree support p q) : d1410 p = d1410 q := by
  simp only [d1410, h 86 (by decide), agree1409 p q h, agree1400 p q h]
theorem nonnegative1410 (p : Pattern) : 0 ≤ d1410 p :=
  nonnegative_ite (p 86) (nonnegative1409 p) (nonnegative1400 p)
def d1411 (p : Pattern) : Int := if p 80 then d1410 p else d1398 p
theorem agree1411 (p q : Pattern) (h : Agree support p q) : d1411 p = d1411 q := by
  simp only [d1411, h 80 (by decide), agree1410 p q h, agree1398 p q h]
theorem nonnegative1411 (p : Pattern) : 0 ≤ d1411 p :=
  nonnegative_ite (p 80) (nonnegative1410 p) (nonnegative1398 p)
def d1412 (p : Pattern) : Int := if p 158 then d1167 p else d0 p
theorem agree1412 (p q : Pattern) (h : Agree support p q) : d1412 p = d1412 q := by
  simp only [d1412, h 158 (by decide), agree1167 p q h, agree0 p q h]
theorem nonnegative1412 (p : Pattern) : 0 ≤ d1412 p :=
  nonnegative_ite (p 158) (nonnegative1167 p) (nonnegative0 p)
def d1413 (p : Pattern) : Int := if p 139 then d11 p else d5 p
theorem agree1413 (p q : Pattern) (h : Agree support p q) : d1413 p = d1413 q := by
  simp only [d1413, h 139 (by decide), agree11 p q h, agree5 p q h]
theorem nonnegative1413 (p : Pattern) : 0 ≤ d1413 p :=
  nonnegative_ite (p 139) (nonnegative11 p) (nonnegative5 p)
def d1414 (p : Pattern) : Int := if p 138 then d1413 p else d5 p
theorem agree1414 (p q : Pattern) (h : Agree support p q) : d1414 p = d1414 q := by
  simp only [d1414, h 138 (by decide), agree1413 p q h, agree5 p q h]
theorem nonnegative1414 (p : Pattern) : 0 ≤ d1414 p :=
  nonnegative_ite (p 138) (nonnegative1413 p) (nonnegative5 p)
def d1415 (p : Pattern) : Int := if p 139 then d21 p else d17 p
theorem agree1415 (p q : Pattern) (h : Agree support p q) : d1415 p = d1415 q := by
  simp only [d1415, h 139 (by decide), agree21 p q h, agree17 p q h]
theorem nonnegative1415 (p : Pattern) : 0 ≤ d1415 p :=
  nonnegative_ite (p 139) (nonnegative21 p) (nonnegative17 p)
def d1416 (p : Pattern) : Int := if p 138 then d1415 p else d17 p
theorem agree1416 (p q : Pattern) (h : Agree support p q) : d1416 p = d1416 q := by
  simp only [d1416, h 138 (by decide), agree1415 p q h, agree17 p q h]
theorem nonnegative1416 (p : Pattern) : 0 ≤ d1416 p :=
  nonnegative_ite (p 138) (nonnegative1415 p) (nonnegative17 p)
def d1417 (p : Pattern) : Int := if p 134 then d1416 p else d1414 p
theorem agree1417 (p q : Pattern) (h : Agree support p q) : d1417 p = d1417 q := by
  simp only [d1417, h 134 (by decide), agree1416 p q h, agree1414 p q h]
theorem nonnegative1417 (p : Pattern) : 0 ≤ d1417 p :=
  nonnegative_ite (p 134) (nonnegative1416 p) (nonnegative1414 p)
def d1418 (p : Pattern) : Int := if p 133 then d1417 p else d1414 p
theorem agree1418 (p q : Pattern) (h : Agree support p q) : d1418 p = d1418 q := by
  simp only [d1418, h 133 (by decide), agree1417 p q h, agree1414 p q h]
theorem nonnegative1418 (p : Pattern) : 0 ≤ d1418 p :=
  nonnegative_ite (p 133) (nonnegative1417 p) (nonnegative1414 p)
def d1419 (p : Pattern) : Int := if p 139 then d21 p else d30 p
theorem agree1419 (p q : Pattern) (h : Agree support p q) : d1419 p = d1419 q := by
  simp only [d1419, h 139 (by decide), agree21 p q h, agree30 p q h]
theorem nonnegative1419 (p : Pattern) : 0 ≤ d1419 p :=
  nonnegative_ite (p 139) (nonnegative21 p) (nonnegative30 p)
def d1420 (p : Pattern) : Int := if p 138 then d1419 p else d30 p
theorem agree1420 (p q : Pattern) (h : Agree support p q) : d1420 p = d1420 q := by
  simp only [d1420, h 138 (by decide), agree1419 p q h, agree30 p q h]
theorem nonnegative1420 (p : Pattern) : 0 ≤ d1420 p :=
  nonnegative_ite (p 138) (nonnegative1419 p) (nonnegative30 p)
def d1421 (p : Pattern) : Int := if p 134 then d1420 p else d1414 p
theorem agree1421 (p q : Pattern) (h : Agree support p q) : d1421 p = d1421 q := by
  simp only [d1421, h 134 (by decide), agree1420 p q h, agree1414 p q h]
theorem nonnegative1421 (p : Pattern) : 0 ≤ d1421 p :=
  nonnegative_ite (p 134) (nonnegative1420 p) (nonnegative1414 p)
def d1422 (p : Pattern) : Int := if p 133 then d1417 p else d1421 p
theorem agree1422 (p q : Pattern) (h : Agree support p q) : d1422 p = d1422 q := by
  simp only [d1422, h 133 (by decide), agree1417 p q h, agree1421 p q h]
theorem nonnegative1422 (p : Pattern) : 0 ≤ d1422 p :=
  nonnegative_ite (p 133) (nonnegative1417 p) (nonnegative1421 p)
def d1423 (p : Pattern) : Int := if p 132 then d1422 p else d1418 p
theorem agree1423 (p q : Pattern) (h : Agree support p q) : d1423 p = d1423 q := by
  simp only [d1423, h 132 (by decide), agree1422 p q h, agree1418 p q h]
theorem nonnegative1423 (p : Pattern) : 0 ≤ d1423 p :=
  nonnegative_ite (p 132) (nonnegative1422 p) (nonnegative1418 p)
def d1424 (p : Pattern) : Int := if p 134 then d1415 p else d1413 p
theorem agree1424 (p q : Pattern) (h : Agree support p q) : d1424 p = d1424 q := by
  simp only [d1424, h 134 (by decide), agree1415 p q h, agree1413 p q h]
theorem nonnegative1424 (p : Pattern) : 0 ≤ d1424 p :=
  nonnegative_ite (p 134) (nonnegative1415 p) (nonnegative1413 p)
def d1425 (p : Pattern) : Int := if p 133 then d1424 p else d1413 p
theorem agree1425 (p q : Pattern) (h : Agree support p q) : d1425 p = d1425 q := by
  simp only [d1425, h 133 (by decide), agree1424 p q h, agree1413 p q h]
theorem nonnegative1425 (p : Pattern) : 0 ≤ d1425 p :=
  nonnegative_ite (p 133) (nonnegative1424 p) (nonnegative1413 p)
def d1426 (p : Pattern) : Int := if p 134 then d1419 p else d1413 p
theorem agree1426 (p q : Pattern) (h : Agree support p q) : d1426 p = d1426 q := by
  simp only [d1426, h 134 (by decide), agree1419 p q h, agree1413 p q h]
theorem nonnegative1426 (p : Pattern) : 0 ≤ d1426 p :=
  nonnegative_ite (p 134) (nonnegative1419 p) (nonnegative1413 p)
def d1427 (p : Pattern) : Int := if p 133 then d1424 p else d1426 p
theorem agree1427 (p q : Pattern) (h : Agree support p q) : d1427 p = d1427 q := by
  simp only [d1427, h 133 (by decide), agree1424 p q h, agree1426 p q h]
theorem nonnegative1427 (p : Pattern) : 0 ≤ d1427 p :=
  nonnegative_ite (p 133) (nonnegative1424 p) (nonnegative1426 p)
def d1428 (p : Pattern) : Int := if p 132 then d1427 p else d1425 p
theorem agree1428 (p q : Pattern) (h : Agree support p q) : d1428 p = d1428 q := by
  simp only [d1428, h 132 (by decide), agree1427 p q h, agree1425 p q h]
theorem nonnegative1428 (p : Pattern) : 0 ≤ d1428 p :=
  nonnegative_ite (p 132) (nonnegative1427 p) (nonnegative1425 p)
def d1429 (p : Pattern) : Int := if p 139 then d2 p else d5 p
theorem agree1429 (p q : Pattern) (h : Agree support p q) : d1429 p = d1429 q := by
  simp only [d1429, h 139 (by decide), agree2 p q h, agree5 p q h]
theorem nonnegative1429 (p : Pattern) : 0 ≤ d1429 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative5 p)
def d1430 (p : Pattern) : Int := if p 138 then d1429 p else d1413 p
theorem agree1430 (p q : Pattern) (h : Agree support p q) : d1430 p = d1430 q := by
  simp only [d1430, h 138 (by decide), agree1429 p q h, agree1413 p q h]
theorem nonnegative1430 (p : Pattern) : 0 ≤ d1430 p :=
  nonnegative_ite (p 138) (nonnegative1429 p) (nonnegative1413 p)
def d1431 (p : Pattern) : Int := if p 139 then d2 p else d17 p
theorem agree1431 (p q : Pattern) (h : Agree support p q) : d1431 p = d1431 q := by
  simp only [d1431, h 139 (by decide), agree2 p q h, agree17 p q h]
theorem nonnegative1431 (p : Pattern) : 0 ≤ d1431 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative17 p)
def d1432 (p : Pattern) : Int := if p 138 then d1431 p else d1415 p
theorem agree1432 (p q : Pattern) (h : Agree support p q) : d1432 p = d1432 q := by
  simp only [d1432, h 138 (by decide), agree1431 p q h, agree1415 p q h]
theorem nonnegative1432 (p : Pattern) : 0 ≤ d1432 p :=
  nonnegative_ite (p 138) (nonnegative1431 p) (nonnegative1415 p)
def d1433 (p : Pattern) : Int := if p 134 then d1432 p else d1430 p
theorem agree1433 (p q : Pattern) (h : Agree support p q) : d1433 p = d1433 q := by
  simp only [d1433, h 134 (by decide), agree1432 p q h, agree1430 p q h]
theorem nonnegative1433 (p : Pattern) : 0 ≤ d1433 p :=
  nonnegative_ite (p 134) (nonnegative1432 p) (nonnegative1430 p)
def d1434 (p : Pattern) : Int := if p 133 then d1433 p else d1430 p
theorem agree1434 (p q : Pattern) (h : Agree support p q) : d1434 p = d1434 q := by
  simp only [d1434, h 133 (by decide), agree1433 p q h, agree1430 p q h]
theorem nonnegative1434 (p : Pattern) : 0 ≤ d1434 p :=
  nonnegative_ite (p 133) (nonnegative1433 p) (nonnegative1430 p)
def d1435 (p : Pattern) : Int := if p 139 then d2 p else d30 p
theorem agree1435 (p q : Pattern) (h : Agree support p q) : d1435 p = d1435 q := by
  simp only [d1435, h 139 (by decide), agree2 p q h, agree30 p q h]
theorem nonnegative1435 (p : Pattern) : 0 ≤ d1435 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative30 p)
def d1436 (p : Pattern) : Int := if p 138 then d1435 p else d1419 p
theorem agree1436 (p q : Pattern) (h : Agree support p q) : d1436 p = d1436 q := by
  simp only [d1436, h 138 (by decide), agree1435 p q h, agree1419 p q h]
theorem nonnegative1436 (p : Pattern) : 0 ≤ d1436 p :=
  nonnegative_ite (p 138) (nonnegative1435 p) (nonnegative1419 p)
def d1437 (p : Pattern) : Int := if p 134 then d1436 p else d1430 p
theorem agree1437 (p q : Pattern) (h : Agree support p q) : d1437 p = d1437 q := by
  simp only [d1437, h 134 (by decide), agree1436 p q h, agree1430 p q h]
theorem nonnegative1437 (p : Pattern) : 0 ≤ d1437 p :=
  nonnegative_ite (p 134) (nonnegative1436 p) (nonnegative1430 p)
def d1438 (p : Pattern) : Int := if p 133 then d1433 p else d1437 p
theorem agree1438 (p q : Pattern) (h : Agree support p q) : d1438 p = d1438 q := by
  simp only [d1438, h 133 (by decide), agree1433 p q h, agree1437 p q h]
theorem nonnegative1438 (p : Pattern) : 0 ≤ d1438 p :=
  nonnegative_ite (p 133) (nonnegative1433 p) (nonnegative1437 p)
def d1439 (p : Pattern) : Int := if p 132 then d1438 p else d1434 p
theorem agree1439 (p q : Pattern) (h : Agree support p q) : d1439 p = d1439 q := by
  simp only [d1439, h 132 (by decide), agree1438 p q h, agree1434 p q h]
theorem nonnegative1439 (p : Pattern) : 0 ≤ d1439 p :=
  nonnegative_ite (p 132) (nonnegative1438 p) (nonnegative1434 p)
end NetHack.Sokoban32Refined
