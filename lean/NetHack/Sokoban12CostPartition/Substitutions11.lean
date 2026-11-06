/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1320 (p : Pattern) : d0 (change p 134 (some 108)) = d0 p := by
  rfl
theorem sub1321 (p : Pattern) : d2 (change p 134 (some 108)) = d2 p := by
  rfl
theorem sub1322 (p : Pattern) : d6 (change p 134 (some 108)) = d6 p := by
  change (if p 193 then d2 (change p 134 (some 108)) else d0 (change p 134 (some 108))) = d6 p
  rw [sub1321, sub1320]
  rfl
theorem sub1323 (p : Pattern) : d7 (change p 134 (some 108)) = d7 p := by
  change (if p 192 then d6 (change p 134 (some 108)) else d0 (change p 134 (some 108))) = d7 p
  rw [sub1322, sub1320]
  rfl
theorem sub1324 (p : Pattern) : d4 (change p 134 (some 108)) = d4 p := by
  rfl
theorem sub1325 (p : Pattern) : d54 (change p 134 (some 108)) = d54 p := by
  change (if p 193 then d4 (change p 134 (some 108)) else d2 (change p 134 (some 108))) = d54 p
  rw [sub1324, sub1321]
  rfl
theorem sub1326 (p : Pattern) : d55 (change p 134 (some 108)) = d55 p := by
  change (if p 192 then d54 (change p 134 (some 108)) else d2 (change p 134 (some 108))) = d55 p
  rw [sub1325, sub1321]
  rfl
theorem sub1327 (p : Pattern) : d56 (change p 134 (some 108)) = d56 p := by
  change (if p 186 then d55 (change p 134 (some 108)) else d7 (change p 134 (some 108))) = d56 p
  rw [sub1326, sub1323]
  rfl
theorem sub1328 (p : Pattern) : d57 (change p 134 (some 108)) = d57 p := by
  change (if p 160 then d56 (change p 134 (some 108)) else d7 (change p 134 (some 108))) = d57 p
  rw [sub1327, sub1323]
  rfl
theorem sub1329 (p : Pattern) : d1 (change p 134 (some 108)) = d1 p := by
  rfl
theorem sub1330 (p : Pattern) : d8 (change p 134 (some 108)) = d8 p := by
  change (if p 271 then d1 (change p 134 (some 108)) else d0 (change p 134 (some 108))) = d8 p
  rw [sub1329, sub1320]
  rfl
theorem sub1331 (p : Pattern) : d3 (change p 134 (some 108)) = d3 p := by
  rfl
theorem sub1332 (p : Pattern) : d9 (change p 134 (some 108)) = d9 p := by
  change (if p 271 then d3 (change p 134 (some 108)) else d2 (change p 134 (some 108))) = d9 p
  rw [sub1331, sub1321]
  rfl
theorem sub1333 (p : Pattern) : d10 (change p 134 (some 108)) = d10 p := by
  change (if p 193 then d9 (change p 134 (some 108)) else d8 (change p 134 (some 108))) = d10 p
  rw [sub1332, sub1330]
  rfl
theorem sub1334 (p : Pattern) : d11 (change p 134 (some 108)) = d11 p := by
  change (if p 192 then d10 (change p 134 (some 108)) else d8 (change p 134 (some 108))) = d11 p
  rw [sub1333, sub1330]
  rfl
theorem sub1335 (p : Pattern) : d12 (change p 134 (some 108)) = d12 p := by
  change (if p 168 then d11 (change p 134 (some 108)) else d7 (change p 134 (some 108))) = d12 p
  rw [sub1334, sub1323]
  rfl
theorem sub1336 (p : Pattern) : d5 (change p 134 (some 108)) = d5 p := by
  rfl
theorem sub1337 (p : Pattern) : d58 (change p 134 (some 108)) = d58 p := by
  change (if p 271 then d5 (change p 134 (some 108)) else d4 (change p 134 (some 108))) = d58 p
  rw [sub1336, sub1324]
  rfl
theorem sub1338 (p : Pattern) : d59 (change p 134 (some 108)) = d59 p := by
  change (if p 193 then d58 (change p 134 (some 108)) else d9 (change p 134 (some 108))) = d59 p
  rw [sub1337, sub1332]
  rfl
theorem sub1339 (p : Pattern) : d60 (change p 134 (some 108)) = d60 p := by
  change (if p 192 then d59 (change p 134 (some 108)) else d9 (change p 134 (some 108))) = d60 p
  rw [sub1338, sub1332]
  rfl
theorem sub1340 (p : Pattern) : d61 (change p 134 (some 108)) = d61 p := by
  change (if p 186 then d60 (change p 134 (some 108)) else d11 (change p 134 (some 108))) = d61 p
  rw [sub1339, sub1334]
  rfl
theorem sub1341 (p : Pattern) : d62 (change p 134 (some 108)) = d62 p := by
  change (if p 168 then d61 (change p 134 (some 108)) else d56 (change p 134 (some 108))) = d62 p
  rw [sub1340, sub1327]
  rfl
theorem sub1342 (p : Pattern) : d63 (change p 134 (some 108)) = d63 p := by
  change (if p 160 then d62 (change p 134 (some 108)) else d12 (change p 134 (some 108))) = d63 p
  rw [sub1341, sub1335]
  rfl
theorem sub1343 (p : Pattern) : d64 (change p 134 (some 108)) = d64 p := by
  change (if p 141 then d63 (change p 134 (some 108)) else d57 (change p 134 (some 108))) = d64 p
  rw [sub1342, sub1328]
  rfl
theorem sub1344 (p : Pattern) : d67 (change p 134 (some 108)) = d64 p := by
  change d64 (change p 134 (some 108)) = d64 p
  exact sub1343 p
theorem sub1345 (p : Pattern) : d68 (change p 134 (some 108)) = d68 p := by
  change (if p 158 then d55 (change p 134 (some 108)) else d57 (change p 134 (some 108))) = d68 p
  rw [sub1326, sub1328]
  rfl
theorem sub1346 (p : Pattern) : d65 (change p 134 (some 108)) = d65 p := by
  change (if p 168 then d60 (change p 134 (some 108)) else d55 (change p 134 (some 108))) = d65 p
  rw [sub1339, sub1326]
  rfl
theorem sub1347 (p : Pattern) : d69 (change p 134 (some 108)) = d69 p := by
  change (if p 158 then d65 (change p 134 (some 108)) else d63 (change p 134 (some 108))) = d69 p
  rw [sub1346, sub1342]
  rfl
theorem sub1348 (p : Pattern) : d70 (change p 134 (some 108)) = d70 p := by
  change (if p 141 then d69 (change p 134 (some 108)) else d68 (change p 134 (some 108))) = d70 p
  rw [sub1347, sub1345]
  rfl
theorem sub1349 (p : Pattern) : d71 (change p 134 (some 108)) = d70 p := by
  change d70 (change p 134 (some 108)) = d70 p
  exact sub1348 p
theorem sub1350 (p : Pattern) : d72 (change p 134 (some 108)) = d811 p := by
  change (if p 133 then d71 (change p 134 (some 108)) else d67 (change p 134 (some 108))) = d811 p
  rw [sub1349, sub1344]
  rfl
theorem sub1351 (p : Pattern) : d66 (change p 134 (some 108)) = d66 p := by
  change (if p 141 then d65 (change p 134 (some 108)) else d55 (change p 134 (some 108))) = d66 p
  rw [sub1346, sub1326]
  rfl
theorem sub1352 (p : Pattern) : d73 (change p 134 (some 108)) = d812 p := by
  change (if p 133 then d66 (change p 134 (some 108)) else d71 (change p 134 (some 108))) = d812 p
  rw [sub1351, sub1349]
  rfl
theorem sub1353 (p : Pattern) : d74 (change p 134 (some 108)) = d813 p := by
  change (if p 132 then d73 (change p 134 (some 108)) else d72 (change p 134 (some 108))) = d813 p
  rw [sub1352, sub1350]
  rfl
theorem sub1354 (p : Pattern) : d0 (change p 186 none) = d0 p := by
  rfl
theorem sub1355 (p : Pattern) : d2 (change p 186 none) = d2 p := by
  rfl
theorem sub1356 (p : Pattern) : d6 (change p 186 none) = d6 p := by
  change (if p 193 then d2 (change p 186 none) else d0 (change p 186 none)) = d6 p
  rw [sub1355, sub1354]
  rfl
theorem sub1357 (p : Pattern) : d7 (change p 186 none) = d7 p := by
  change (if p 192 then d6 (change p 186 none) else d0 (change p 186 none)) = d7 p
  rw [sub1356, sub1354]
  rfl
theorem sub1358 (p : Pattern) : d56 (change p 186 none) = d7 p := by
  change d7 (change p 186 none) = d7 p
  exact sub1357 p
theorem sub1359 (p : Pattern) : d1 (change p 186 none) = d1 p := by
  rfl
theorem sub1360 (p : Pattern) : d8 (change p 186 none) = d8 p := by
  change (if p 271 then d1 (change p 186 none) else d0 (change p 186 none)) = d8 p
  rw [sub1359, sub1354]
  rfl
theorem sub1361 (p : Pattern) : d3 (change p 186 none) = d3 p := by
  rfl
theorem sub1362 (p : Pattern) : d9 (change p 186 none) = d9 p := by
  change (if p 271 then d3 (change p 186 none) else d2 (change p 186 none)) = d9 p
  rw [sub1361, sub1355]
  rfl
theorem sub1363 (p : Pattern) : d10 (change p 186 none) = d10 p := by
  change (if p 193 then d9 (change p 186 none) else d8 (change p 186 none)) = d10 p
  rw [sub1362, sub1360]
  rfl
theorem sub1364 (p : Pattern) : d11 (change p 186 none) = d11 p := by
  change (if p 192 then d10 (change p 186 none) else d8 (change p 186 none)) = d11 p
  rw [sub1363, sub1360]
  rfl
theorem sub1365 (p : Pattern) : d61 (change p 186 none) = d11 p := by
  change d11 (change p 186 none) = d11 p
  exact sub1364 p
theorem sub1366 (p : Pattern) : d62 (change p 186 none) = d12 p := by
  change (if p 168 then d61 (change p 186 none) else d56 (change p 186 none)) = d12 p
  rw [sub1365, sub1358]
  rfl
theorem sub1367 (p : Pattern) : d451 (change p 186 none) = d13 p := by
  change (if p 141 then d62 (change p 186 none) else d56 (change p 186 none)) = d13 p
  rw [sub1366, sub1358]
  rfl
theorem sub1368 (p : Pattern) : d4 (change p 186 none) = d4 p := by
  rfl
theorem sub1369 (p : Pattern) : d54 (change p 186 none) = d54 p := by
  change (if p 193 then d4 (change p 186 none) else d2 (change p 186 none)) = d54 p
  rw [sub1368, sub1355]
  rfl
theorem sub1370 (p : Pattern) : d55 (change p 186 none) = d55 p := by
  change (if p 192 then d54 (change p 186 none) else d2 (change p 186 none)) = d55 p
  rw [sub1369, sub1355]
  rfl
theorem sub1371 (p : Pattern) : d452 (change p 186 none) = d106 p := by
  change (if p 160 then d55 (change p 186 none) else d56 (change p 186 none)) = d106 p
  rw [sub1370, sub1358]
  rfl
theorem sub1372 (p : Pattern) : d5 (change p 186 none) = d5 p := by
  rfl
theorem sub1373 (p : Pattern) : d58 (change p 186 none) = d58 p := by
  change (if p 271 then d5 (change p 186 none) else d4 (change p 186 none)) = d58 p
  rw [sub1372, sub1368]
  rfl
theorem sub1374 (p : Pattern) : d59 (change p 186 none) = d59 p := by
  change (if p 193 then d58 (change p 186 none) else d9 (change p 186 none)) = d59 p
  rw [sub1373, sub1362]
  rfl
theorem sub1375 (p : Pattern) : d60 (change p 186 none) = d60 p := by
  change (if p 192 then d59 (change p 186 none) else d9 (change p 186 none)) = d60 p
  rw [sub1374, sub1362]
  rfl
theorem sub1376 (p : Pattern) : d65 (change p 186 none) = d65 p := by
  change (if p 168 then d60 (change p 186 none) else d55 (change p 186 none)) = d65 p
  rw [sub1375, sub1370]
  rfl
theorem sub1377 (p : Pattern) : d453 (change p 186 none) = d109 p := by
  change (if p 160 then d65 (change p 186 none) else d62 (change p 186 none)) = d109 p
  rw [sub1376, sub1366]
  rfl
theorem sub1378 (p : Pattern) : d454 (change p 186 none) = d227 p := by
  change (if p 141 then d453 (change p 186 none) else d452 (change p 186 none)) = d227 p
  rw [sub1377, sub1371]
  rfl
theorem sub1379 (p : Pattern) : d455 (change p 186 none) = d1018 p := by
  change (if p 134 then d454 (change p 186 none) else d451 (change p 186 none)) = d1018 p
  rw [sub1378, sub1367]
  rfl
theorem sub1380 (p : Pattern) : d456 (change p 186 none) = d832 p := by
  change (if p 158 then d55 (change p 186 none) else d56 (change p 186 none)) = d832 p
  rw [sub1370, sub1358]
  rfl
theorem sub1381 (p : Pattern) : d457 (change p 186 none) = d833 p := by
  change (if p 158 then d65 (change p 186 none) else d62 (change p 186 none)) = d833 p
  rw [sub1376, sub1366]
  rfl
theorem sub1382 (p : Pattern) : d458 (change p 186 none) = d834 p := by
  change (if p 141 then d457 (change p 186 none) else d456 (change p 186 none)) = d834 p
  rw [sub1381, sub1380]
  rfl
theorem sub1383 (p : Pattern) : d459 (change p 186 none) = d229 p := by
  change (if p 158 then d55 (change p 186 none) else d452 (change p 186 none)) = d229 p
  rw [sub1370, sub1371]
  rfl
theorem sub1384 (p : Pattern) : d460 (change p 186 none) = d230 p := by
  change (if p 158 then d65 (change p 186 none) else d453 (change p 186 none)) = d230 p
  rw [sub1376, sub1377]
  rfl
theorem sub1385 (p : Pattern) : d461 (change p 186 none) = d231 p := by
  change (if p 141 then d460 (change p 186 none) else d459 (change p 186 none)) = d231 p
  rw [sub1384, sub1383]
  rfl
theorem sub1386 (p : Pattern) : d462 (change p 186 none) = d1019 p := by
  change (if p 134 then d461 (change p 186 none) else d458 (change p 186 none)) = d1019 p
  rw [sub1385, sub1382]
  rfl
theorem sub1387 (p : Pattern) : d463 (change p 186 none) = d1020 p := by
  change (if p 133 then d462 (change p 186 none) else d455 (change p 186 none)) = d1020 p
  rw [sub1386, sub1379]
  rfl
theorem sub1388 (p : Pattern) : d66 (change p 186 none) = d66 p := by
  change (if p 141 then d65 (change p 186 none) else d55 (change p 186 none)) = d66 p
  rw [sub1376, sub1370]
  rfl
theorem sub1389 (p : Pattern) : d464 (change p 186 none) = d1021 p := by
  change (if p 133 then d66 (change p 186 none) else d462 (change p 186 none)) = d1021 p
  rw [sub1388, sub1386]
  rfl
theorem sub1390 (p : Pattern) : d465 (change p 186 none) = d1022 p := by
  change (if p 132 then d464 (change p 186 none) else d463 (change p 186 none)) = d1022 p
  rw [sub1389, sub1387]
  rfl
theorem sub1391 (p : Pattern) : d119 (change p 186 none) = d119 p := by
  change (if p 187 then d55 (change p 186 none) else d7 (change p 186 none)) = d119 p
  rw [sub1370, sub1357]
  rfl
theorem sub1392 (p : Pattern) : d137 (change p 186 none) = d119 p := by
  change d119 (change p 186 none) = d119 p
  exact sub1391 p
theorem sub1393 (p : Pattern) : d466 (change p 186 none) = d1023 p := by
  change (if p 160 then d137 (change p 186 none) else d56 (change p 186 none)) = d1023 p
  rw [sub1392, sub1358]
  rfl
theorem sub1394 (p : Pattern) : d467 (change p 186 none) = d1024 p := by
  change (if p 159 then d466 (change p 186 none) else d56 (change p 186 none)) = d1024 p
  rw [sub1393, sub1358]
  rfl
theorem sub1395 (p : Pattern) : d468 (change p 186 none) = d1025 p := by
  change (if p 158 then d467 (change p 186 none) else d56 (change p 186 none)) = d1025 p
  rw [sub1394, sub1358]
  rfl
theorem sub1396 (p : Pattern) : d125 (change p 186 none) = d125 p := by
  change (if p 187 then d60 (change p 186 none) else d11 (change p 186 none)) = d125 p
  rw [sub1375, sub1364]
  rfl
theorem sub1397 (p : Pattern) : d143 (change p 186 none) = d125 p := by
  change d125 (change p 186 none) = d125 p
  exact sub1396 p
theorem sub1398 (p : Pattern) : d144 (change p 186 none) = d502 p := by
  change (if p 168 then d143 (change p 186 none) else d137 (change p 186 none)) = d502 p
  rw [sub1397, sub1392]
  rfl
theorem sub1399 (p : Pattern) : d469 (change p 186 none) = d1026 p := by
  change (if p 160 then d144 (change p 186 none) else d62 (change p 186 none)) = d1026 p
  rw [sub1398, sub1366]
  rfl
theorem sub1400 (p : Pattern) : d470 (change p 186 none) = d1027 p := by
  change (if p 159 then d469 (change p 186 none) else d62 (change p 186 none)) = d1027 p
  rw [sub1399, sub1366]
  rfl
theorem sub1401 (p : Pattern) : d471 (change p 186 none) = d1028 p := by
  change (if p 158 then d470 (change p 186 none) else d62 (change p 186 none)) = d1028 p
  rw [sub1400, sub1366]
  rfl
theorem sub1402 (p : Pattern) : d472 (change p 186 none) = d1029 p := by
  change (if p 141 then d471 (change p 186 none) else d468 (change p 186 none)) = d1029 p
  rw [sub1401, sub1395]
  rfl
theorem sub1403 (p : Pattern) : d473 (change p 186 none) = d1030 p := by
  change (if p 134 then d66 (change p 186 none) else d472 (change p 186 none)) = d1030 p
  rw [sub1388, sub1402]
  rfl
theorem sub1404 (p : Pattern) : d474 (change p 186 none) = d1031 p := by
  change (if p 158 then d55 (change p 186 none) else d466 (change p 186 none)) = d1031 p
  rw [sub1370, sub1393]
  rfl
theorem sub1405 (p : Pattern) : d475 (change p 186 none) = d1032 p := by
  change (if p 158 then d65 (change p 186 none) else d469 (change p 186 none)) = d1032 p
  rw [sub1376, sub1399]
  rfl
theorem sub1406 (p : Pattern) : d476 (change p 186 none) = d1033 p := by
  change (if p 141 then d475 (change p 186 none) else d474 (change p 186 none)) = d1033 p
  rw [sub1405, sub1404]
  rfl
theorem sub1407 (p : Pattern) : d477 (change p 186 none) = d1034 p := by
  change (if p 134 then d66 (change p 186 none) else d476 (change p 186 none)) = d1034 p
  rw [sub1388, sub1406]
  rfl
theorem sub1408 (p : Pattern) : d478 (change p 186 none) = d1035 p := by
  change (if p 133 then d477 (change p 186 none) else d473 (change p 186 none)) = d1035 p
  rw [sub1407, sub1403]
  rfl
theorem sub1409 (p : Pattern) : d479 (change p 186 none) = d1036 p := by
  change (if p 158 then d55 (change p 186 none) else d467 (change p 186 none)) = d1036 p
  rw [sub1370, sub1394]
  rfl
theorem sub1410 (p : Pattern) : d480 (change p 186 none) = d1037 p := by
  change (if p 158 then d65 (change p 186 none) else d470 (change p 186 none)) = d1037 p
  rw [sub1376, sub1400]
  rfl
theorem sub1411 (p : Pattern) : d481 (change p 186 none) = d1038 p := by
  change (if p 141 then d480 (change p 186 none) else d479 (change p 186 none)) = d1038 p
  rw [sub1410, sub1409]
  rfl
theorem sub1412 (p : Pattern) : d482 (change p 186 none) = d1039 p := by
  change (if p 134 then d66 (change p 186 none) else d481 (change p 186 none)) = d1039 p
  rw [sub1388, sub1411]
  rfl
theorem sub1413 (p : Pattern) : d483 (change p 186 none) = d1040 p := by
  change (if p 133 then d66 (change p 186 none) else d482 (change p 186 none)) = d1040 p
  rw [sub1388, sub1412]
  rfl
theorem sub1414 (p : Pattern) : d484 (change p 186 none) = d1041 p := by
  change (if p 132 then d483 (change p 186 none) else d478 (change p 186 none)) = d1041 p
  rw [sub1413, sub1408]
  rfl
theorem sub1415 (p : Pattern) : d485 (change p 186 none) = d1042 p := by
  change (if p 108 then d484 (change p 186 none) else d465 (change p 186 none)) = d1042 p
  rw [sub1414, sub1390]
  rfl
theorem sub1416 (p : Pattern) : d0 (change p 159 (some 158)) = d0 p := by
  rfl
theorem sub1417 (p : Pattern) : d2 (change p 159 (some 158)) = d2 p := by
  rfl
theorem sub1418 (p : Pattern) : d6 (change p 159 (some 158)) = d6 p := by
  change (if p 193 then d2 (change p 159 (some 158)) else d0 (change p 159 (some 158))) = d6 p
  rw [sub1417, sub1416]
  rfl
theorem sub1419 (p : Pattern) : d7 (change p 159 (some 158)) = d7 p := by
  change (if p 192 then d6 (change p 159 (some 158)) else d0 (change p 159 (some 158))) = d7 p
  rw [sub1418, sub1416]
  rfl
theorem sub1420 (p : Pattern) : d4 (change p 159 (some 158)) = d4 p := by
  rfl
theorem sub1421 (p : Pattern) : d54 (change p 159 (some 158)) = d54 p := by
  change (if p 193 then d4 (change p 159 (some 158)) else d2 (change p 159 (some 158))) = d54 p
  rw [sub1420, sub1417]
  rfl
theorem sub1422 (p : Pattern) : d55 (change p 159 (some 158)) = d55 p := by
  change (if p 192 then d54 (change p 159 (some 158)) else d2 (change p 159 (some 158))) = d55 p
  rw [sub1421, sub1417]
  rfl
theorem sub1423 (p : Pattern) : d56 (change p 159 (some 158)) = d56 p := by
  change (if p 186 then d55 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d56 p
  rw [sub1422, sub1419]
  rfl
theorem sub1424 (p : Pattern) : d57 (change p 159 (some 158)) = d57 p := by
  change (if p 160 then d56 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d57 p
  rw [sub1423, sub1419]
  rfl
theorem sub1425 (p : Pattern) : d114 (change p 159 (some 158)) = d57 p := by
  change d57 (change p 159 (some 158)) = d57 p
  exact sub1424 p
theorem sub1426 (p : Pattern) : d1 (change p 159 (some 158)) = d1 p := by
  rfl
theorem sub1427 (p : Pattern) : d8 (change p 159 (some 158)) = d8 p := by
  change (if p 271 then d1 (change p 159 (some 158)) else d0 (change p 159 (some 158))) = d8 p
  rw [sub1426, sub1416]
  rfl
theorem sub1428 (p : Pattern) : d3 (change p 159 (some 158)) = d3 p := by
  rfl
theorem sub1429 (p : Pattern) : d9 (change p 159 (some 158)) = d9 p := by
  change (if p 271 then d3 (change p 159 (some 158)) else d2 (change p 159 (some 158))) = d9 p
  rw [sub1428, sub1417]
  rfl
theorem sub1430 (p : Pattern) : d10 (change p 159 (some 158)) = d10 p := by
  change (if p 193 then d9 (change p 159 (some 158)) else d8 (change p 159 (some 158))) = d10 p
  rw [sub1429, sub1427]
  rfl
theorem sub1431 (p : Pattern) : d11 (change p 159 (some 158)) = d11 p := by
  change (if p 192 then d10 (change p 159 (some 158)) else d8 (change p 159 (some 158))) = d11 p
  rw [sub1430, sub1427]
  rfl
theorem sub1432 (p : Pattern) : d12 (change p 159 (some 158)) = d12 p := by
  change (if p 168 then d11 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d12 p
  rw [sub1431, sub1419]
  rfl
theorem sub1433 (p : Pattern) : d5 (change p 159 (some 158)) = d5 p := by
  rfl
theorem sub1434 (p : Pattern) : d58 (change p 159 (some 158)) = d58 p := by
  change (if p 271 then d5 (change p 159 (some 158)) else d4 (change p 159 (some 158))) = d58 p
  rw [sub1433, sub1420]
  rfl
theorem sub1435 (p : Pattern) : d59 (change p 159 (some 158)) = d59 p := by
  change (if p 193 then d58 (change p 159 (some 158)) else d9 (change p 159 (some 158))) = d59 p
  rw [sub1434, sub1429]
  rfl
theorem sub1436 (p : Pattern) : d60 (change p 159 (some 158)) = d60 p := by
  change (if p 192 then d59 (change p 159 (some 158)) else d9 (change p 159 (some 158))) = d60 p
  rw [sub1435, sub1429]
  rfl
theorem sub1437 (p : Pattern) : d61 (change p 159 (some 158)) = d61 p := by
  change (if p 186 then d60 (change p 159 (some 158)) else d11 (change p 159 (some 158))) = d61 p
  rw [sub1436, sub1431]
  rfl
theorem sub1438 (p : Pattern) : d62 (change p 159 (some 158)) = d62 p := by
  change (if p 168 then d61 (change p 159 (some 158)) else d56 (change p 159 (some 158))) = d62 p
  rw [sub1437, sub1423]
  rfl
theorem sub1439 (p : Pattern) : d63 (change p 159 (some 158)) = d63 p := by
  change (if p 160 then d62 (change p 159 (some 158)) else d12 (change p 159 (some 158))) = d63 p
  rw [sub1438, sub1432]
  rfl
end NetHack.Sokoban12CostPartition
