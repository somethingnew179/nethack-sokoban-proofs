/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions08
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1350 (pattern : Twelve) : d1421 (change pattern 4 12) = d2011 pattern := by
  change (if pattern.d then d1418 (change pattern 4 12) else d1417 (change pattern 4 12)) = d2011 pattern
  rw [s1349, s1347]
  simp only [ite_self]
theorem s1351 (pattern : Twelve) : d119 (change pattern 4 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 4 12) else d3 (change pattern 4 12)) = d119 pattern
  rw [s1340, s1270]
  rfl
theorem s1352 (pattern : Twelve) : d1281 (change pattern 4 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 4 12) else d872 (change pattern 4 12)) = d1281 pattern
  rw [s1351, s1333]
  rfl
theorem s1353 (pattern : Twelve) : d1287 (change pattern 4 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 4 12) else d1279 (change pattern 4 12)) = d1287 pattern
  rw [s1352, s1342]
  rfl
theorem s1354 (pattern : Twelve) : d1297 (change pattern 4 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 4 12) else d34 (change pattern 4 12)) = d1297 pattern
  rw [s1353, s1273]
  rfl
theorem s1355 (pattern : Twelve) : d1415 (change pattern 4 12) = d1297 pattern := by
  change d1297 (change pattern 4 12) = d1297 pattern
  exact s1354 pattern
theorem s1356 (pattern : Twelve) : d40 (change pattern 4 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d23 (change pattern 4 12)) = d40 pattern
  rw [s1267, s1272]
  rfl
theorem s1357 (pattern : Twelve) : d830 (change pattern 4 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 4 12) else d41 (change pattern 4 12)) = d830 pattern
  rw [s1356, s1294]
  rfl
theorem s1358 (pattern : Twelve) : d14 (change pattern 4 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 4 12) else d5 (change pattern 4 12)) = d14 pattern
  rw [s1267, s1291]
  rfl
theorem s1359 (pattern : Twelve) : d1277 (change pattern 4 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 4 12) else d15 (change pattern 4 12)) = d1277 pattern
  rw [s1358, s1292]
  rfl
theorem s1360 (pattern : Twelve) : d1282 (change pattern 4 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 4 12) else d1276 (change pattern 4 12)) = d1282 pattern
  rw [s1359, s1341]
  rfl
theorem s1361 (pattern : Twelve) : d125 (change pattern 4 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d119 (change pattern 4 12)) = d125 pattern
  rw [s1267, s1351]
  rfl
theorem s1362 (pattern : Twelve) : d1288 (change pattern 4 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 4 12) else d1282 (change pattern 4 12)) = d1288 pattern
  rw [s1361, s1360]
  rfl
theorem s1363 (pattern : Twelve) : d1299 (change pattern 4 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 4 12) else d830 (change pattern 4 12)) = d1299 pattern
  rw [s1362, s1357]
  rfl
theorem s1364 (pattern : Twelve) : d1416 (change pattern 4 12) = d1299 pattern := by
  change d1299 (change pattern 4 12) = d1299 pattern
  exact s1363 pattern
theorem s1365 (pattern : Twelve) : d1419 (change pattern 4 12) = d2012 pattern := by
  change (if pattern.j then d1416 (change pattern 4 12) else d1415 (change pattern 4 12)) = d2012 pattern
  rw [s1364, s1355]
  rfl
theorem s1366 (pattern : Twelve) : d1420 (change pattern 4 12) = d2013 pattern := by
  change (if pattern.j then d6 (change pattern 4 12) else d1413 (change pattern 4 12)) = d2013 pattern
  rw [s1267, s1346]
  rfl
theorem s1367 (pattern : Twelve) : d1422 (change pattern 4 12) = d2014 pattern := by
  change (if pattern.d then d1420 (change pattern 4 12) else d1419 (change pattern 4 12)) = d2014 pattern
  rw [s1366, s1365]
  rfl
theorem s1368 (pattern : Twelve) : d1423 (change pattern 4 12) = d2015 pattern := by
  change (if pattern.c then d1422 (change pattern 4 12) else d1421 (change pattern 4 12)) = d2015 pattern
  rw [s1367, s1350]
  rfl
theorem s1369 (pattern : Twelve) : d1424 (change pattern 4 12) = d2015 pattern := by
  change (if pattern.c then d1422 (change pattern 4 12) else d1418 (change pattern 4 12)) = d2015 pattern
  rw [s1367, s1349]
  rfl
theorem s1370 (pattern : Twelve) : d1425 (change pattern 4 12) = d2015 pattern := by
  change (if pattern.g then d1424 (change pattern 4 12) else d1423 (change pattern 4 12)) = d2015 pattern
  rw [s1369, s1368]
  simp only [ite_self]
theorem s1371 (pattern : Twelve) : d1426 (change pattern 4 12) = d2015 pattern := by
  change (if pattern.b then d1424 (change pattern 4 12) else d1425 (change pattern 4 12)) = d2015 pattern
  rw [s1369, s1370]
  simp only [ite_self]
theorem s1372 (pattern : Twelve) : d1427 (change pattern 4 12) = d2015 pattern := by
  change (if pattern.a then d1424 (change pattern 4 12) else d1426 (change pattern 4 12)) = d2015 pattern
  rw [s1369, s1371]
  simp only [ite_self]
theorem s1373 (pattern : Twelve) : d10 (change pattern 4 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 4 12) else d0 (change pattern 4 12)) = d10 pattern
  rw [s1265, s1255]
  rfl
theorem s1374 (pattern : Twelve) : d11 (change pattern 4 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 4 12) else d1 (change pattern 4 12)) = d11 pattern
  rw [s1270, s1256]
  rfl
theorem s1375 (pattern : Twelve) : d19 (change pattern 4 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 4 12) else d10 (change pattern 4 12)) = d19 pattern
  rw [s1374, s1373]
  rfl
theorem s1376 (pattern : Twelve) : d16 (change pattern 4 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 4 12) else d2 (change pattern 4 12)) = d16 pattern
  rw [s1287, s1265]
  rfl
theorem s1377 (pattern : Twelve) : d1324 (change pattern 4 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 4 12) else d11 (change pattern 4 12)) = d1324 pattern
  rw [s1376, s1374]
  rfl
theorem s1378 (pattern : Twelve) : d1649 (change pattern 4 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 4 12) else d19 (change pattern 4 12)) = d1649 pattern
  rw [s1377, s1375]
  rfl
theorem s1379 (pattern : Twelve) : d1705 (change pattern 4 12) = d1649 pattern := by
  change d1649 (change pattern 4 12) = d1649 pattern
  exact s1378 pattern
theorem s1380 (pattern : Twelve) : d12 (change pattern 4 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 4 12) else d3 (change pattern 4 12)) = d12 pattern
  rw [s1291, s1270]
  rfl
theorem s1381 (pattern : Twelve) : d25 (change pattern 4 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 4 12) else d16 (change pattern 4 12)) = d25 pattern
  rw [s1380, s1376]
  rfl
theorem s1382 (pattern : Twelve) : d817 (change pattern 4 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 4 12) else d19 (change pattern 4 12)) = d817 pattern
  rw [s1381, s1375]
  rfl
theorem s1383 (pattern : Twelve) : d29 (change pattern 4 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d19 (change pattern 4 12)) = d29 pattern
  rw [s1267, s1375]
  rfl
theorem s1384 (pattern : Twelve) : d1286 (change pattern 4 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 4 12) else d817 (change pattern 4 12)) = d1286 pattern
  rw [s1383, s1382]
  rfl
theorem s1385 (pattern : Twelve) : d13 (change pattern 4 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 4 12) else d4 (change pattern 4 12)) = d13 pattern
  rw [s1267, s1287]
  rfl
theorem s1386 (pattern : Twelve) : d20 (change pattern 4 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 4 12) else d12 (change pattern 4 12)) = d20 pattern
  rw [s1385, s1380]
  rfl
theorem s1387 (pattern : Twelve) : d1644 (change pattern 4 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 4 12) else d1324 (change pattern 4 12)) = d1644 pattern
  rw [s1386, s1377]
  rfl
theorem s1388 (pattern : Twelve) : d1645 (change pattern 4 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d1324 (change pattern 4 12)) = d1645 pattern
  rw [s1267, s1377]
  rfl
theorem s1389 (pattern : Twelve) : d1647 (change pattern 4 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 4 12) else d1644 (change pattern 4 12)) = d1647 pattern
  rw [s1388, s1387]
  rfl
theorem s1390 (pattern : Twelve) : d1651 (change pattern 4 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 4 12) else d1286 (change pattern 4 12)) = d1651 pattern
  rw [s1389, s1384]
  rfl
theorem s1391 (pattern : Twelve) : d1706 (change pattern 4 12) = d1651 pattern := by
  change d1651 (change pattern 4 12) = d1651 pattern
  exact s1390 pattern
theorem s1392 (pattern : Twelve) : d1709 (change pattern 4 12) = d2016 pattern := by
  change (if pattern.j then d1706 (change pattern 4 12) else d1705 (change pattern 4 12)) = d2016 pattern
  rw [s1391, s1379]
  rfl
theorem s1393 (pattern : Twelve) : d1652 (change pattern 4 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 4 12) else d817 (change pattern 4 12)) = d1652 pattern
  rw [s1387, s1382]
  rfl
theorem s1394 (pattern : Twelve) : d1707 (change pattern 4 12) = d1652 pattern := by
  change d1652 (change pattern 4 12) = d1652 pattern
  exact s1393 pattern
theorem s1395 (pattern : Twelve) : d21 (change pattern 4 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 4 12) else d13 (change pattern 4 12)) = d21 pattern
  rw [s1358, s1385]
  rfl
theorem s1396 (pattern : Twelve) : d821 (change pattern 4 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 4 12) else d25 (change pattern 4 12)) = d821 pattern
  rw [s1395, s1381]
  rfl
theorem s1397 (pattern : Twelve) : d42 (change pattern 4 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d25 (change pattern 4 12)) = d42 pattern
  rw [s1267, s1381]
  rfl
theorem s1398 (pattern : Twelve) : d1289 (change pattern 4 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 4 12) else d821 (change pattern 4 12)) = d1289 pattern
  rw [s1397, s1396]
  rfl
theorem s1399 (pattern : Twelve) : d22 (change pattern 4 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 4 12) else d14 (change pattern 4 12)) = d22 pattern
  rw [s1267, s1358]
  rfl
theorem s1400 (pattern : Twelve) : d1646 (change pattern 4 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 4 12) else d20 (change pattern 4 12)) = d1646 pattern
  rw [s1399, s1386]
  rfl
theorem s1401 (pattern : Twelve) : d128 (change pattern 4 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d20 (change pattern 4 12)) = d128 pattern
  rw [s1267, s1386]
  rfl
theorem s1402 (pattern : Twelve) : d1648 (change pattern 4 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 4 12) else d1646 (change pattern 4 12)) = d1648 pattern
  rw [s1401, s1400]
  rfl
theorem s1403 (pattern : Twelve) : d1654 (change pattern 4 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 4 12) else d1289 (change pattern 4 12)) = d1654 pattern
  rw [s1402, s1398]
  rfl
theorem s1404 (pattern : Twelve) : d1708 (change pattern 4 12) = d1654 pattern := by
  change d1654 (change pattern 4 12) = d1654 pattern
  exact s1403 pattern
theorem s1405 (pattern : Twelve) : d1710 (change pattern 4 12) = d2017 pattern := by
  change (if pattern.j then d1708 (change pattern 4 12) else d1707 (change pattern 4 12)) = d2017 pattern
  rw [s1404, s1394]
  rfl
theorem s1406 (pattern : Twelve) : d1711 (change pattern 4 12) = d2018 pattern := by
  change (if pattern.j then d6 (change pattern 4 12) else d1706 (change pattern 4 12)) = d2018 pattern
  rw [s1267, s1391]
  rfl
theorem s1407 (pattern : Twelve) : d1712 (change pattern 4 12) = d2019 pattern := by
  change (if pattern.d then d1711 (change pattern 4 12) else d1710 (change pattern 4 12)) = d2019 pattern
  rw [s1406, s1405]
  rfl
theorem s1408 (pattern : Twelve) : d1713 (change pattern 4 12) = d2020 pattern := by
  change (if pattern.c then d1712 (change pattern 4 12) else d1709 (change pattern 4 12)) = d2020 pattern
  rw [s1407, s1392]
  rfl
theorem s1409 (pattern : Twelve) : d0 (change pattern 4 5) = d0 pattern := by
  rfl
theorem s1410 (pattern : Twelve) : d1 (change pattern 4 5) = d1 pattern := by
  rfl
theorem s1411 (pattern : Twelve) : d26 (change pattern 4 5) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 4 5) else d0 (change pattern 4 5)) = d26 pattern
  rw [s1410, s1409]
  rfl
theorem s1412 (pattern : Twelve) : d7 (change pattern 4 5) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 4 5) else d0 (change pattern 4 5)) = d7 pattern
  rw [s1410, s1409]
  rfl
theorem s1413 (pattern : Twelve) : d17 (change pattern 4 5) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 4 5) else d0 (change pattern 4 5)) = d17 pattern
  rw [s1412, s1409]
  rfl
theorem s1414 (pattern : Twelve) : d27 (change pattern 4 5) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 4 5) else d17 (change pattern 4 5)) = d27 pattern
  rw [s1410, s1413]
  rfl
theorem s1415 (pattern : Twelve) : d50 (change pattern 4 5) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 4 5) else d26 (change pattern 4 5)) = d50 pattern
  rw [s1414, s1411]
  rfl
theorem s1416 (pattern : Twelve) : d72 (change pattern 4 5) = d50 pattern := by
  change d50 (change pattern 4 5) = d50 pattern
  exact s1415 pattern
theorem s1417 (pattern : Twelve) : d304 (change pattern 4 5) = d50 pattern := by
  change d72 (change pattern 4 5) = d50 pattern
  exact s1416 pattern
theorem s1418 (pattern : Twelve) : d2 (change pattern 4 5) = d2 pattern := by
  rfl
theorem s1419 (pattern : Twelve) : d30 (change pattern 4 5) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 4 5) else d0 (change pattern 4 5)) = d30 pattern
  rw [s1418, s1409]
  rfl
theorem s1420 (pattern : Twelve) : d4 (change pattern 4 5) = d4 pattern := by
  rfl
theorem s1421 (pattern : Twelve) : d6 (change pattern 4 5) = d6 pattern := by
  rfl
theorem s1422 (pattern : Twelve) : d13 (change pattern 4 5) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 4 5) else d4 (change pattern 4 5)) = d13 pattern
  rw [s1421, s1420]
  rfl
theorem s1423 (pattern : Twelve) : d5 (change pattern 4 5) = d5 pattern := by
  rfl
theorem s1424 (pattern : Twelve) : d14 (change pattern 4 5) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 4 5) else d5 (change pattern 4 5)) = d14 pattern
  rw [s1421, s1423]
  rfl
theorem s1425 (pattern : Twelve) : d21 (change pattern 4 5) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 4 5) else d13 (change pattern 4 5)) = d21 pattern
  rw [s1424, s1422]
  rfl
theorem s1426 (pattern : Twelve) : d32 (change pattern 4 5) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 4 5) else d17 (change pattern 4 5)) = d32 pattern
  rw [s1425, s1413]
  rfl
theorem s1427 (pattern : Twelve) : d53 (change pattern 4 5) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 4 5) else d30 (change pattern 4 5)) = d53 pattern
  rw [s1426, s1419]
  rfl
theorem s1428 (pattern : Twelve) : d74 (change pattern 4 5) = d53 pattern := by
  change d53 (change pattern 4 5) = d53 pattern
  exact s1427 pattern
theorem s1429 (pattern : Twelve) : d305 (change pattern 4 5) = d53 pattern := by
  change d74 (change pattern 4 5) = d53 pattern
  exact s1428 pattern
theorem s1430 (pattern : Twelve) : d320 (change pattern 4 5) = d2021 pattern := by
  change (if pattern.j then d305 (change pattern 4 5) else d304 (change pattern 4 5)) = d2021 pattern
  rw [s1429, s1417]
  rfl
theorem s1431 (pattern : Twelve) : d306 (change pattern 4 5) = d50 pattern := by
  change d72 (change pattern 4 5) = d50 pattern
  exact s1416 pattern
theorem s1432 (pattern : Twelve) : d36 (change pattern 4 5) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d17 (change pattern 4 5)) = d36 pattern
  rw [s1421, s1413]
  rfl
theorem s1433 (pattern : Twelve) : d57 (change pattern 4 5) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 4 5) else d30 (change pattern 4 5)) = d57 pattern
  rw [s1432, s1419]
  rfl
theorem s1434 (pattern : Twelve) : d77 (change pattern 4 5) = d57 pattern := by
  change d57 (change pattern 4 5) = d57 pattern
  exact s1433 pattern
theorem s1435 (pattern : Twelve) : d307 (change pattern 4 5) = d57 pattern := by
  change d77 (change pattern 4 5) = d57 pattern
  exact s1434 pattern
theorem s1436 (pattern : Twelve) : d321 (change pattern 4 5) = d2022 pattern := by
  change (if pattern.j then d307 (change pattern 4 5) else d306 (change pattern 4 5)) = d2022 pattern
  rw [s1435, s1431]
  rfl
theorem s1437 (pattern : Twelve) : d332 (change pattern 4 5) = d2023 pattern := by
  change (if pattern.d then d321 (change pattern 4 5) else d320 (change pattern 4 5)) = d2023 pattern
  rw [s1436, s1430]
  rfl
theorem s1438 (pattern : Twelve) : d3 (change pattern 4 5) = d3 pattern := by
  rfl
theorem s1439 (pattern : Twelve) : d37 (change pattern 4 5) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 4 5) else d17 (change pattern 4 5)) = d37 pattern
  rw [s1438, s1413]
  rfl
theorem s1440 (pattern : Twelve) : d58 (change pattern 4 5) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 4 5) else d30 (change pattern 4 5)) = d58 pattern
  rw [s1439, s1419]
  rfl
theorem s1441 (pattern : Twelve) : d79 (change pattern 4 5) = d58 pattern := by
  change d58 (change pattern 4 5) = d58 pattern
  exact s1440 pattern
theorem s1442 (pattern : Twelve) : d308 (change pattern 4 5) = d58 pattern := by
  change d79 (change pattern 4 5) = d58 pattern
  exact s1441 pattern
theorem s1443 (pattern : Twelve) : d38 (change pattern 4 5) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 4 5) else d2 (change pattern 4 5)) = d38 pattern
  rw [s1420, s1418]
  rfl
theorem s1444 (pattern : Twelve) : d9 (change pattern 4 5) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 4 5) else d2 (change pattern 4 5)) = d9 pattern
  rw [s1438, s1418]
  rfl
theorem s1445 (pattern : Twelve) : d23 (change pattern 4 5) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 4 5) else d2 (change pattern 4 5)) = d23 pattern
  rw [s1444, s1418]
  rfl
theorem s1446 (pattern : Twelve) : d40 (change pattern 4 5) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d23 (change pattern 4 5)) = d40 pattern
  rw [s1421, s1445]
  rfl
theorem s1447 (pattern : Twelve) : d60 (change pattern 4 5) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 4 5) else d38 (change pattern 4 5)) = d60 pattern
  rw [s1446, s1443]
  rfl
theorem s1448 (pattern : Twelve) : d81 (change pattern 4 5) = d60 pattern := by
  change d60 (change pattern 4 5) = d60 pattern
  exact s1447 pattern
theorem s1449 (pattern : Twelve) : d309 (change pattern 4 5) = d60 pattern := by
  change d81 (change pattern 4 5) = d60 pattern
  exact s1448 pattern
theorem s1450 (pattern : Twelve) : d322 (change pattern 4 5) = d2024 pattern := by
  change (if pattern.j then d309 (change pattern 4 5) else d308 (change pattern 4 5)) = d2024 pattern
  rw [s1449, s1442]
  rfl
theorem s1451 (pattern : Twelve) : d310 (change pattern 4 5) = d57 pattern := by
  change d77 (change pattern 4 5) = d57 pattern
  exact s1434 pattern
theorem s1452 (pattern : Twelve) : d323 (change pattern 4 5) = d2025 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d310 (change pattern 4 5)) = d2025 pattern
  rw [s1421, s1451]
  rfl
theorem s1453 (pattern : Twelve) : d333 (change pattern 4 5) = d2026 pattern := by
  change (if pattern.d then d323 (change pattern 4 5) else d322 (change pattern 4 5)) = d2026 pattern
  rw [s1452, s1450]
  rfl
theorem s1454 (pattern : Twelve) : d338 (change pattern 4 5) = d2027 pattern := by
  change (if pattern.c then d333 (change pattern 4 5) else d332 (change pattern 4 5)) = d2027 pattern
  rw [s1453, s1437]
  rfl
theorem s1455 (pattern : Twelve) : d311 (change pattern 4 5) = d50 pattern := by
  change d72 (change pattern 4 5) = d50 pattern
  exact s1416 pattern
theorem s1456 (pattern : Twelve) : d43 (change pattern 4 5) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 4 5) else d1 (change pattern 4 5)) = d43 pattern
  rw [s1425, s1410]
  rfl
theorem s1457 (pattern : Twelve) : d62 (change pattern 4 5) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 4 5) else d30 (change pattern 4 5)) = d62 pattern
  rw [s1456, s1419]
  rfl
theorem s1458 (pattern : Twelve) : d83 (change pattern 4 5) = d62 pattern := by
  change d62 (change pattern 4 5) = d62 pattern
  exact s1457 pattern
theorem s1459 (pattern : Twelve) : d312 (change pattern 4 5) = d62 pattern := by
  change d83 (change pattern 4 5) = d62 pattern
  exact s1458 pattern
theorem s1460 (pattern : Twelve) : d324 (change pattern 4 5) = d2028 pattern := by
  change (if pattern.j then d312 (change pattern 4 5) else d311 (change pattern 4 5)) = d2028 pattern
  rw [s1459, s1455]
  rfl
theorem s1461 (pattern : Twelve) : d45 (change pattern 4 5) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d1 (change pattern 4 5)) = d45 pattern
  rw [s1421, s1410]
  rfl
theorem s1462 (pattern : Twelve) : d65 (change pattern 4 5) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 4 5) else d30 (change pattern 4 5)) = d65 pattern
  rw [s1461, s1419]
  rfl
theorem s1463 (pattern : Twelve) : d85 (change pattern 4 5) = d65 pattern := by
  change d65 (change pattern 4 5) = d65 pattern
  exact s1462 pattern
theorem s1464 (pattern : Twelve) : d313 (change pattern 4 5) = d65 pattern := by
  change d85 (change pattern 4 5) = d65 pattern
  exact s1463 pattern
theorem s1465 (pattern : Twelve) : d325 (change pattern 4 5) = d2029 pattern := by
  change (if pattern.j then d313 (change pattern 4 5) else d311 (change pattern 4 5)) = d2029 pattern
  rw [s1464, s1455]
  rfl
theorem s1466 (pattern : Twelve) : d334 (change pattern 4 5) = d2030 pattern := by
  change (if pattern.d then d325 (change pattern 4 5) else d324 (change pattern 4 5)) = d2030 pattern
  rw [s1465, s1460]
  rfl
theorem s1467 (pattern : Twelve) : d46 (change pattern 4 5) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 4 5) else d1 (change pattern 4 5)) = d46 pattern
  rw [s1438, s1410]
  rfl
theorem s1468 (pattern : Twelve) : d67 (change pattern 4 5) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 4 5) else d30 (change pattern 4 5)) = d67 pattern
  rw [s1467, s1419]
  rfl
theorem s1469 (pattern : Twelve) : d87 (change pattern 4 5) = d67 pattern := by
  change d67 (change pattern 4 5) = d67 pattern
  exact s1468 pattern
theorem s1470 (pattern : Twelve) : d314 (change pattern 4 5) = d67 pattern := by
  change d87 (change pattern 4 5) = d67 pattern
  exact s1469 pattern
theorem s1471 (pattern : Twelve) : d47 (change pattern 4 5) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d3 (change pattern 4 5)) = d47 pattern
  rw [s1421, s1438]
  rfl
theorem s1472 (pattern : Twelve) : d69 (change pattern 4 5) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 4 5) else d38 (change pattern 4 5)) = d69 pattern
  rw [s1471, s1443]
  rfl
theorem s1473 (pattern : Twelve) : d89 (change pattern 4 5) = d69 pattern := by
  change d69 (change pattern 4 5) = d69 pattern
  exact s1472 pattern
theorem s1474 (pattern : Twelve) : d315 (change pattern 4 5) = d69 pattern := by
  change d89 (change pattern 4 5) = d69 pattern
  exact s1473 pattern
theorem s1475 (pattern : Twelve) : d326 (change pattern 4 5) = d2031 pattern := by
  change (if pattern.j then d315 (change pattern 4 5) else d314 (change pattern 4 5)) = d2031 pattern
  rw [s1474, s1470]
  rfl
theorem s1476 (pattern : Twelve) : d327 (change pattern 4 5) = d2032 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d313 (change pattern 4 5)) = d2032 pattern
  rw [s1421, s1464]
  rfl
theorem s1477 (pattern : Twelve) : d335 (change pattern 4 5) = d2033 pattern := by
  change (if pattern.d then d327 (change pattern 4 5) else d326 (change pattern 4 5)) = d2033 pattern
  rw [s1476, s1475]
  rfl
theorem s1478 (pattern : Twelve) : d339 (change pattern 4 5) = d2034 pattern := by
  change (if pattern.c then d335 (change pattern 4 5) else d334 (change pattern 4 5)) = d2034 pattern
  rw [s1477, s1466]
  rfl
theorem s1479 (pattern : Twelve) : d341 (change pattern 4 5) = d2035 pattern := by
  change (if pattern.g then d339 (change pattern 4 5) else d338 (change pattern 4 5)) = d2035 pattern
  rw [s1478, s1454]
  rfl
theorem s1480 (pattern : Twelve) : d316 (change pattern 4 5) = d53 pattern := by
  change d74 (change pattern 4 5) = d53 pattern
  exact s1428 pattern
theorem s1481 (pattern : Twelve) : d328 (change pattern 4 5) = d2021 pattern := by
  change (if pattern.j then d316 (change pattern 4 5) else d311 (change pattern 4 5)) = d2021 pattern
  rw [s1480, s1455]
  rfl
theorem s1482 (pattern : Twelve) : d317 (change pattern 4 5) = d57 pattern := by
  change d77 (change pattern 4 5) = d57 pattern
  exact s1434 pattern
theorem s1483 (pattern : Twelve) : d329 (change pattern 4 5) = d2022 pattern := by
  change (if pattern.j then d317 (change pattern 4 5) else d311 (change pattern 4 5)) = d2022 pattern
  rw [s1482, s1455]
  rfl
theorem s1484 (pattern : Twelve) : d336 (change pattern 4 5) = d2023 pattern := by
  change (if pattern.d then d329 (change pattern 4 5) else d328 (change pattern 4 5)) = d2023 pattern
  rw [s1483, s1481]
  rfl
theorem s1485 (pattern : Twelve) : d318 (change pattern 4 5) = d58 pattern := by
  change d79 (change pattern 4 5) = d58 pattern
  exact s1441 pattern
theorem s1486 (pattern : Twelve) : d319 (change pattern 4 5) = d60 pattern := by
  change d81 (change pattern 4 5) = d60 pattern
  exact s1448 pattern
theorem s1487 (pattern : Twelve) : d330 (change pattern 4 5) = d2024 pattern := by
  change (if pattern.j then d319 (change pattern 4 5) else d318 (change pattern 4 5)) = d2024 pattern
  rw [s1486, s1485]
  rfl
theorem s1488 (pattern : Twelve) : d331 (change pattern 4 5) = d2025 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d317 (change pattern 4 5)) = d2025 pattern
  rw [s1421, s1482]
  rfl
theorem s1489 (pattern : Twelve) : d337 (change pattern 4 5) = d2026 pattern := by
  change (if pattern.d then d331 (change pattern 4 5) else d330 (change pattern 4 5)) = d2026 pattern
  rw [s1488, s1487]
  rfl
theorem s1490 (pattern : Twelve) : d340 (change pattern 4 5) = d2027 pattern := by
  change (if pattern.c then d337 (change pattern 4 5) else d336 (change pattern 4 5)) = d2027 pattern
  rw [s1489, s1484]
  rfl
theorem s1491 (pattern : Twelve) : d342 (change pattern 4 5) = d2035 pattern := by
  change (if pattern.g then d339 (change pattern 4 5) else d340 (change pattern 4 5)) = d2035 pattern
  rw [s1478, s1490]
  rfl
theorem s1492 (pattern : Twelve) : d343 (change pattern 4 5) = d2035 pattern := by
  change (if pattern.b then d342 (change pattern 4 5) else d341 (change pattern 4 5)) = d2035 pattern
  rw [s1491, s1479]
  simp only [ite_self]
theorem s1493 (pattern : Twelve) : d344 (change pattern 4 5) = d2035 pattern := by
  change (if pattern.a then d342 (change pattern 4 5) else d343 (change pattern 4 5)) = d2035 pattern
  rw [s1491, s1492]
  simp only [ite_self]
theorem s1494 (pattern : Twelve) : d814 (change pattern 4 5) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 4 5) else d7 (change pattern 4 5)) = d814 pattern
  rw [s1410, s1412]
  rfl
theorem s1495 (pattern : Twelve) : d816 (change pattern 4 5) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 4 5) else d814 (change pattern 4 5)) = d816 pattern
  rw [s1410, s1494]
  rfl
theorem s1496 (pattern : Twelve) : d824 (change pattern 4 5) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 4 5) else d27 (change pattern 4 5)) = d824 pattern
  rw [s1495, s1414]
  rfl
theorem s1497 (pattern : Twelve) : d838 (change pattern 4 5) = d824 pattern := by
  change d824 (change pattern 4 5) = d824 pattern
  exact s1496 pattern
theorem s1498 (pattern : Twelve) : d980 (change pattern 4 5) = d824 pattern := by
  change d838 (change pattern 4 5) = d824 pattern
  exact s1497 pattern
theorem s1499 (pattern : Twelve) : d34 (change pattern 4 5) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 4 5) else d17 (change pattern 4 5)) = d34 pattern
  rw [s1445, s1413]
  rfl
end NetHack.Sokoban21.Diagram
