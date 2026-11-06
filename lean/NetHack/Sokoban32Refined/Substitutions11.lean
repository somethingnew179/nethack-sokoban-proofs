/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1320 (p : Pattern) : d125 (change p 139 none) = d1109 p := by
  change (if p 133 then d75 (change p 139 none) else d109 (change p 139 none)) = d1109 p
  rw [sub1294, sub1315]
  rfl
theorem sub1321 (p : Pattern) : d507 (change p 139 none) = d1110 p := by
  change (if p 132 then d125 (change p 139 none) else d503 (change p 139 none)) = d1110 p
  rw [sub1320, sub1316]
  rfl
theorem sub1322 (p : Pattern) : d508 (change p 139 none) = d1110 p := by
  change (if p 113 then d507 (change p 139 none) else d506 (change p 139 none)) = d1110 p
  rw [sub1321, sub1319]
  simp only [ite_self]
theorem sub1323 (p : Pattern) : d509 (change p 139 none) = d1111 p := by
  change (if p 112 then d508 (change p 139 none) else d499 (change p 139 none)) = d1111 p
  rw [sub1322, sub1308]
  rfl
theorem sub1324 (p : Pattern) : d510 (change p 139 none) = d8 p := by
  change (if p 134 then d52 (change p 139 none) else d484 (change p 139 none)) = d8 p
  rw [sub1237, sub1292]
  simp only [ite_self]
theorem sub1325 (p : Pattern) : d511 (change p 139 none) = d1098 p := by
  change (if p 133 then d470 (change p 139 none) else d510 (change p 139 none)) = d1098 p
  rw [sub1266, sub1324]
  rfl
theorem sub1326 (p : Pattern) : d512 (change p 139 none) = d1105 p := by
  change (if p 132 then d491 (change p 139 none) else d511 (change p 139 none)) = d1105 p
  rw [sub1300, sub1325]
  rfl
theorem sub1327 (p : Pattern) : d513 (change p 139 none) = d1105 p := by
  change (if p 113 then d512 (change p 139 none) else d487 (change p 139 none)) = d1105 p
  rw [sub1326, sub1296]
  simp only [ite_self]
theorem sub1328 (p : Pattern) : d111 (change p 139 none) = d1112 p := by
  change (if p 133 then d2 (change p 139 none) else d109 (change p 139 none)) = d1112 p
  rw [sub1229, sub1315]
  rfl
theorem sub1329 (p : Pattern) : d514 (change p 139 none) = d1113 p := by
  change (if p 132 then d111 (change p 139 none) else d503 (change p 139 none)) = d1113 p
  rw [sub1328, sub1316]
  rfl
theorem sub1330 (p : Pattern) : d110 (change p 139 none) = d1108 p := by
  change (if p 133 then d109 (change p 139 none) else d97 (change p 139 none)) = d1108 p
  rw [sub1315, sub1312]
  rfl
theorem sub1331 (p : Pattern) : d112 (change p 139 none) = d1113 p := by
  change (if p 132 then d111 (change p 139 none) else d110 (change p 139 none)) = d1113 p
  rw [sub1328, sub1330]
  rfl
theorem sub1332 (p : Pattern) : d515 (change p 139 none) = d1113 p := by
  change (if p 113 then d112 (change p 139 none) else d514 (change p 139 none)) = d1113 p
  rw [sub1331, sub1329]
  simp only [ite_self]
theorem sub1333 (p : Pattern) : d516 (change p 139 none) = d1114 p := by
  change (if p 112 then d515 (change p 139 none) else d513 (change p 139 none)) = d1114 p
  rw [sub1332, sub1327]
  rfl
theorem sub1334 (p : Pattern) : d517 (change p 139 none) = d1115 p := by
  change (if p 106 then d516 (change p 139 none) else d509 (change p 139 none)) = d1115 p
  rw [sub1333, sub1323]
  rfl
theorem sub1335 (p : Pattern) : d518 (change p 139 none) = d1116 p := by
  change (if p 86 then d517 (change p 139 none) else d495 (change p 139 none)) = d1116 p
  rw [sub1334, sub1304]
  rfl
theorem sub1336 (p : Pattern) : d519 (change p 139 none) = d1099 p := by
  change (if p 134 then d58 (change p 139 none) else d52 (change p 139 none)) = d1099 p
  rw [sub1255, sub1237]
  rfl
theorem sub1337 (p : Pattern) : d520 (change p 139 none) = d1101 p := by
  change (if p 133 then d473 (change p 139 none) else d519 (change p 139 none)) = d1101 p
  rw [sub1269, sub1336]
  rfl
theorem sub1338 (p : Pattern) : d521 (change p 139 none) = d1102 p := by
  change (if p 132 then d520 (change p 139 none) else d471 (change p 139 none)) = d1102 p
  rw [sub1337, sub1267]
  rfl
theorem sub1339 (p : Pattern) : d522 (change p 139 none) = d1102 p := by
  change (if p 113 then d521 (change p 139 none) else d475 (change p 139 none)) = d1102 p
  rw [sub1338, sub1271]
  simp only [ite_self]
theorem sub1340 (p : Pattern) : d523 (change p 139 none) = d1102 p := by
  change (if p 112 then d522 (change p 139 none) else d499 (change p 139 none)) = d1102 p
  rw [sub1339, sub1308]
  simp only [ite_self]
theorem sub1341 (p : Pattern) : d524 (change p 139 none) = d1098 p := by
  change (if p 133 then d470 (change p 139 none) else d52 (change p 139 none)) = d1098 p
  rw [sub1266, sub1237]
  rfl
theorem sub1342 (p : Pattern) : d525 (change p 139 none) = d1105 p := by
  change (if p 132 then d491 (change p 139 none) else d524 (change p 139 none)) = d1105 p
  rw [sub1300, sub1341]
  rfl
theorem sub1343 (p : Pattern) : d526 (change p 139 none) = d1105 p := by
  change (if p 113 then d525 (change p 139 none) else d492 (change p 139 none)) = d1105 p
  rw [sub1342, sub1301]
  simp only [ite_self]
theorem sub1344 (p : Pattern) : d527 (change p 139 none) = d1105 p := by
  change (if p 112 then d526 (change p 139 none) else d513 (change p 139 none)) = d1105 p
  rw [sub1343, sub1327]
  simp only [ite_self]
theorem sub1345 (p : Pattern) : d528 (change p 139 none) = d1106 p := by
  change (if p 106 then d527 (change p 139 none) else d523 (change p 139 none)) = d1106 p
  rw [sub1344, sub1340]
  rfl
theorem sub1346 (p : Pattern) : d529 (change p 139 none) = d1102 p := by
  change (if p 132 then d520 (change p 139 none) else d511 (change p 139 none)) = d1102 p
  rw [sub1337, sub1325]
  rfl
theorem sub1347 (p : Pattern) : d530 (change p 139 none) = d1102 p := by
  change (if p 113 then d529 (change p 139 none) else d498 (change p 139 none)) = d1102 p
  rw [sub1346, sub1307]
  simp only [ite_self]
theorem sub1348 (p : Pattern) : d126 (change p 139 none) = d1110 p := by
  change (if p 132 then d125 (change p 139 none) else d110 (change p 139 none)) = d1110 p
  rw [sub1320, sub1330]
  rfl
theorem sub1349 (p : Pattern) : d531 (change p 139 none) = d1110 p := by
  change (if p 113 then d126 (change p 139 none) else d507 (change p 139 none)) = d1110 p
  rw [sub1348, sub1321]
  simp only [ite_self]
theorem sub1350 (p : Pattern) : d532 (change p 139 none) = d1111 p := by
  change (if p 112 then d531 (change p 139 none) else d530 (change p 139 none)) = d1111 p
  rw [sub1349, sub1347]
  rfl
theorem sub1351 (p : Pattern) : d533 (change p 139 none) = d1105 p := by
  change (if p 113 then d525 (change p 139 none) else d512 (change p 139 none)) = d1105 p
  rw [sub1342, sub1326]
  simp only [ite_self]
theorem sub1352 (p : Pattern) : d130 (change p 139 none) = d1117 p := by
  change (if p 113 then d2 (change p 139 none) else d112 (change p 139 none)) = d1117 p
  rw [sub1229, sub1331]
  rfl
theorem sub1353 (p : Pattern) : d534 (change p 139 none) = d1118 p := by
  change (if p 112 then d130 (change p 139 none) else d533 (change p 139 none)) = d1118 p
  rw [sub1352, sub1351]
  rfl
theorem sub1354 (p : Pattern) : d535 (change p 139 none) = d1119 p := by
  change (if p 106 then d534 (change p 139 none) else d532 (change p 139 none)) = d1119 p
  rw [sub1353, sub1350]
  rfl
theorem sub1355 (p : Pattern) : d536 (change p 139 none) = d1120 p := by
  change (if p 86 then d535 (change p 139 none) else d528 (change p 139 none)) = d1120 p
  rw [sub1354, sub1345]
  rfl
theorem sub1356 (p : Pattern) : d537 (change p 139 none) = d1121 p := by
  change (if p 80 then d536 (change p 139 none) else d518 (change p 139 none)) = d1121 p
  rw [sub1355, sub1335]
  rfl
theorem sub1357 (p : Pattern) : d0 (change p 113 (some 112)) = d0 p := by
  rfl
theorem sub1358 (p : Pattern) : d2 (change p 113 (some 112)) = d2 p := by
  rfl
theorem sub1359 (p : Pattern) : d3 (change p 113 (some 112)) = d3 p := by
  change (if p 161 then d2 (change p 113 (some 112)) else d0 (change p 113 (some 112))) = d3 p
  rw [sub1358, sub1357]
  rfl
theorem sub1360 (p : Pattern) : d4 (change p 113 (some 112)) = d4 p := by
  change (if p 160 then d3 (change p 113 (some 112)) else d0 (change p 113 (some 112))) = d4 p
  rw [sub1359, sub1357]
  rfl
theorem sub1361 (p : Pattern) : d5 (change p 113 (some 112)) = d5 p := by
  change (if p 160 then d2 (change p 113 (some 112)) else d0 (change p 113 (some 112))) = d5 p
  rw [sub1358, sub1357]
  rfl
theorem sub1362 (p : Pattern) : d6 (change p 113 (some 112)) = d6 p := by
  change (if p 159 then d5 (change p 113 (some 112)) else d4 (change p 113 (some 112))) = d6 p
  rw [sub1361, sub1360]
  rfl
theorem sub1363 (p : Pattern) : d7 (change p 113 (some 112)) = d7 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d4 (change p 113 (some 112))) = d7 p
  rw [sub1358, sub1360]
  rfl
theorem sub1364 (p : Pattern) : d8 (change p 113 (some 112)) = d8 p := by
  change (if p 158 then d7 (change p 113 (some 112)) else d6 (change p 113 (some 112))) = d8 p
  rw [sub1363, sub1362]
  rfl
theorem sub1365 (p : Pattern) : d1 (change p 113 (some 112)) = d1 p := by
  rfl
theorem sub1366 (p : Pattern) : d9 (change p 113 (some 112)) = d9 p := by
  change (if p 161 then d2 (change p 113 (some 112)) else d1 (change p 113 (some 112))) = d9 p
  rw [sub1358, sub1365]
  rfl
theorem sub1367 (p : Pattern) : d10 (change p 113 (some 112)) = d10 p := by
  change (if p 160 then d9 (change p 113 (some 112)) else d1 (change p 113 (some 112))) = d10 p
  rw [sub1366, sub1365]
  rfl
theorem sub1368 (p : Pattern) : d11 (change p 113 (some 112)) = d11 p := by
  change (if p 160 then d2 (change p 113 (some 112)) else d1 (change p 113 (some 112))) = d11 p
  rw [sub1358, sub1365]
  rfl
theorem sub1369 (p : Pattern) : d12 (change p 113 (some 112)) = d12 p := by
  change (if p 159 then d11 (change p 113 (some 112)) else d10 (change p 113 (some 112))) = d12 p
  rw [sub1368, sub1367]
  rfl
theorem sub1370 (p : Pattern) : d13 (change p 113 (some 112)) = d13 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d10 (change p 113 (some 112))) = d13 p
  rw [sub1358, sub1367]
  rfl
theorem sub1371 (p : Pattern) : d14 (change p 113 (some 112)) = d14 p := by
  change (if p 158 then d13 (change p 113 (some 112)) else d12 (change p 113 (some 112))) = d14 p
  rw [sub1370, sub1369]
  rfl
theorem sub1372 (p : Pattern) : d15 (change p 113 (some 112)) = d15 p := by
  change (if p 139 then d14 (change p 113 (some 112)) else d8 (change p 113 (some 112))) = d15 p
  rw [sub1371, sub1364]
  rfl
theorem sub1373 (p : Pattern) : d17 (change p 113 (some 112)) = d17 p := by
  change (if p 160 then d2 (change p 113 (some 112)) else d3 (change p 113 (some 112))) = d17 p
  rw [sub1358, sub1359]
  rfl
theorem sub1374 (p : Pattern) : d18 (change p 113 (some 112)) = d18 p := by
  change (if p 159 then d17 (change p 113 (some 112)) else d4 (change p 113 (some 112))) = d18 p
  rw [sub1373, sub1360]
  rfl
theorem sub1375 (p : Pattern) : d19 (change p 113 (some 112)) = d19 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d17 (change p 113 (some 112))) = d19 p
  rw [sub1358, sub1373]
  rfl
theorem sub1376 (p : Pattern) : d20 (change p 113 (some 112)) = d20 p := by
  change (if p 158 then d19 (change p 113 (some 112)) else d18 (change p 113 (some 112))) = d20 p
  rw [sub1375, sub1374]
  rfl
theorem sub1377 (p : Pattern) : d21 (change p 113 (some 112)) = d21 p := by
  change (if p 160 then d2 (change p 113 (some 112)) else d9 (change p 113 (some 112))) = d21 p
  rw [sub1358, sub1366]
  rfl
theorem sub1378 (p : Pattern) : d22 (change p 113 (some 112)) = d22 p := by
  change (if p 159 then d21 (change p 113 (some 112)) else d10 (change p 113 (some 112))) = d22 p
  rw [sub1377, sub1367]
  rfl
theorem sub1379 (p : Pattern) : d23 (change p 113 (some 112)) = d23 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d21 (change p 113 (some 112))) = d23 p
  rw [sub1358, sub1377]
  rfl
theorem sub1380 (p : Pattern) : d24 (change p 113 (some 112)) = d24 p := by
  change (if p 158 then d23 (change p 113 (some 112)) else d22 (change p 113 (some 112))) = d24 p
  rw [sub1379, sub1378]
  rfl
theorem sub1381 (p : Pattern) : d25 (change p 113 (some 112)) = d25 p := by
  change (if p 139 then d24 (change p 113 (some 112)) else d20 (change p 113 (some 112))) = d25 p
  rw [sub1380, sub1376]
  rfl
theorem sub1382 (p : Pattern) : d46 (change p 113 (some 112)) = d46 p := by
  change (if p 134 then d25 (change p 113 (some 112)) else d15 (change p 113 (some 112))) = d46 p
  rw [sub1381, sub1372]
  rfl
theorem sub1383 (p : Pattern) : d47 (change p 113 (some 112)) = d47 p := by
  change (if p 133 then d46 (change p 113 (some 112)) else d15 (change p 113 (some 112))) = d47 p
  rw [sub1382, sub1372]
  rfl
theorem sub1384 (p : Pattern) : d29 (change p 113 (some 112)) = d29 p := by
  change (if p 161 then d1 (change p 113 (some 112)) else d0 (change p 113 (some 112))) = d29 p
  rw [sub1365, sub1357]
  rfl
theorem sub1385 (p : Pattern) : d30 (change p 113 (some 112)) = d30 p := by
  change (if p 160 then d2 (change p 113 (some 112)) else d29 (change p 113 (some 112))) = d30 p
  rw [sub1358, sub1384]
  rfl
theorem sub1386 (p : Pattern) : d31 (change p 113 (some 112)) = d31 p := by
  change (if p 159 then d30 (change p 113 (some 112)) else d4 (change p 113 (some 112))) = d31 p
  rw [sub1385, sub1360]
  rfl
theorem sub1387 (p : Pattern) : d32 (change p 113 (some 112)) = d32 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d30 (change p 113 (some 112))) = d32 p
  rw [sub1358, sub1385]
  rfl
theorem sub1388 (p : Pattern) : d33 (change p 113 (some 112)) = d33 p := by
  change (if p 158 then d32 (change p 113 (some 112)) else d31 (change p 113 (some 112))) = d33 p
  rw [sub1387, sub1386]
  rfl
theorem sub1389 (p : Pattern) : d34 (change p 113 (some 112)) = d34 p := by
  change (if p 139 then d24 (change p 113 (some 112)) else d33 (change p 113 (some 112))) = d34 p
  rw [sub1380, sub1388]
  rfl
theorem sub1390 (p : Pattern) : d48 (change p 113 (some 112)) = d48 p := by
  change (if p 134 then d34 (change p 113 (some 112)) else d15 (change p 113 (some 112))) = d48 p
  rw [sub1389, sub1372]
  rfl
theorem sub1391 (p : Pattern) : d37 (change p 113 (some 112)) = d37 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d5 (change p 113 (some 112))) = d37 p
  rw [sub1358, sub1361]
  rfl
theorem sub1392 (p : Pattern) : d38 (change p 113 (some 112)) = d38 p := by
  change (if p 158 then d37 (change p 113 (some 112)) else d6 (change p 113 (some 112))) = d38 p
  rw [sub1391, sub1362]
  rfl
theorem sub1393 (p : Pattern) : d39 (change p 113 (some 112)) = d39 p := by
  change (if p 159 then d2 (change p 113 (some 112)) else d11 (change p 113 (some 112))) = d39 p
  rw [sub1358, sub1368]
  rfl
theorem sub1394 (p : Pattern) : d40 (change p 113 (some 112)) = d40 p := by
  change (if p 158 then d39 (change p 113 (some 112)) else d12 (change p 113 (some 112))) = d40 p
  rw [sub1393, sub1369]
  rfl
theorem sub1395 (p : Pattern) : d41 (change p 113 (some 112)) = d41 p := by
  change (if p 139 then d40 (change p 113 (some 112)) else d38 (change p 113 (some 112))) = d41 p
  rw [sub1394, sub1392]
  rfl
theorem sub1396 (p : Pattern) : d49 (change p 113 (some 112)) = d49 p := by
  change (if p 134 then d25 (change p 113 (some 112)) else d41 (change p 113 (some 112))) = d49 p
  rw [sub1381, sub1395]
  rfl
theorem sub1397 (p : Pattern) : d50 (change p 113 (some 112)) = d50 p := by
  change (if p 133 then d49 (change p 113 (some 112)) else d48 (change p 113 (some 112))) = d50 p
  rw [sub1396, sub1390]
  rfl
theorem sub1398 (p : Pattern) : d51 (change p 113 (some 112)) = d51 p := by
  change (if p 132 then d50 (change p 113 (some 112)) else d47 (change p 113 (some 112))) = d51 p
  rw [sub1397, sub1383]
  rfl
theorem sub1399 (p : Pattern) : d229 (change p 113 (some 112)) = d51 p := by
  change d51 (change p 113 (some 112)) = d51 p
  exact sub1398 p
theorem sub1400 (p : Pattern) : d230 (change p 113 (some 112)) = d51 p := by
  change d229 (change p 113 (some 112)) = d51 p
  exact sub1399 p
theorem sub1401 (p : Pattern) : d68 (change p 113 (some 112)) = d68 p := by
  change (if p 139 then d2 (change p 113 (some 112)) else d40 (change p 113 (some 112))) = d68 p
  rw [sub1358, sub1394]
  rfl
theorem sub1402 (p : Pattern) : d70 (change p 113 (some 112)) = d70 p := by
  change (if p 139 then d2 (change p 113 (some 112)) else d24 (change p 113 (some 112))) = d70 p
  rw [sub1358, sub1380]
  rfl
theorem sub1403 (p : Pattern) : d75 (change p 113 (some 112)) = d75 p := by
  change (if p 134 then d70 (change p 113 (some 112)) else d68 (change p 113 (some 112))) = d75 p
  rw [sub1402, sub1401]
  rfl
theorem sub1404 (p : Pattern) : d79 (change p 113 (some 112)) = d79 p := by
  change (if p 133 then d75 (change p 113 (some 112)) else d46 (change p 113 (some 112))) = d79 p
  rw [sub1403, sub1382]
  rfl
theorem sub1405 (p : Pattern) : d80 (change p 113 (some 112)) = d80 p := by
  change (if p 132 then d79 (change p 113 (some 112)) else d47 (change p 113 (some 112))) = d80 p
  rw [sub1404, sub1383]
  rfl
theorem sub1406 (p : Pattern) : d232 (change p 113 (some 112)) = d80 p := by
  change d80 (change p 113 (some 112)) = d80 p
  exact sub1405 p
theorem sub1407 (p : Pattern) : d233 (change p 113 (some 112)) = d80 p := by
  change d232 (change p 113 (some 112)) = d80 p
  exact sub1406 p
theorem sub1408 (p : Pattern) : d234 (change p 113 (some 112)) = d860 p := by
  change (if p 106 then d233 (change p 113 (some 112)) else d230 (change p 113 (some 112))) = d860 p
  rw [sub1407, sub1400]
  rfl
theorem sub1409 (p : Pattern) : d97 (change p 113 (some 112)) = d97 p := by
  change (if p 139 then d2 (change p 113 (some 112)) else d14 (change p 113 (some 112))) = d97 p
  rw [sub1358, sub1371]
  rfl
theorem sub1410 (p : Pattern) : d98 (change p 113 (some 112)) = d98 p := by
  change (if p 138 then d97 (change p 113 (some 112)) else d14 (change p 113 (some 112))) = d98 p
  rw [sub1409, sub1371]
  rfl
theorem sub1411 (p : Pattern) : d71 (change p 113 (some 112)) = d71 p := by
  change (if p 138 then d70 (change p 113 (some 112)) else d24 (change p 113 (some 112))) = d71 p
  rw [sub1402, sub1380]
  rfl
theorem sub1412 (p : Pattern) : d99 (change p 113 (some 112)) = d99 p := by
  change (if p 134 then d71 (change p 113 (some 112)) else d98 (change p 113 (some 112))) = d99 p
  rw [sub1411, sub1410]
  rfl
theorem sub1413 (p : Pattern) : d100 (change p 113 (some 112)) = d100 p := by
  change (if p 133 then d99 (change p 113 (some 112)) else d98 (change p 113 (some 112))) = d100 p
  rw [sub1412, sub1410]
  rfl
theorem sub1414 (p : Pattern) : d69 (change p 113 (some 112)) = d69 p := by
  change (if p 138 then d68 (change p 113 (some 112)) else d40 (change p 113 (some 112))) = d69 p
  rw [sub1401, sub1394]
  rfl
theorem sub1415 (p : Pattern) : d72 (change p 113 (some 112)) = d72 p := by
  change (if p 134 then d71 (change p 113 (some 112)) else d69 (change p 113 (some 112))) = d72 p
  rw [sub1411, sub1414]
  rfl
theorem sub1416 (p : Pattern) : d101 (change p 113 (some 112)) = d101 p := by
  change (if p 133 then d72 (change p 113 (some 112)) else d99 (change p 113 (some 112))) = d101 p
  rw [sub1415, sub1412]
  rfl
theorem sub1417 (p : Pattern) : d102 (change p 113 (some 112)) = d102 p := by
  change (if p 132 then d101 (change p 113 (some 112)) else d100 (change p 113 (some 112))) = d102 p
  rw [sub1416, sub1413]
  rfl
theorem sub1418 (p : Pattern) : d236 (change p 113 (some 112)) = d102 p := by
  change d102 (change p 113 (some 112)) = d102 p
  exact sub1417 p
theorem sub1419 (p : Pattern) : d237 (change p 113 (some 112)) = d102 p := by
  change d236 (change p 113 (some 112)) = d102 p
  exact sub1418 p
theorem sub1420 (p : Pattern) : d107 (change p 113 (some 112)) = d107 p := by
  change (if p 133 then d2 (change p 113 (some 112)) else d99 (change p 113 (some 112))) = d107 p
  rw [sub1358, sub1412]
  rfl
theorem sub1421 (p : Pattern) : d108 (change p 113 (some 112)) = d108 p := by
  change (if p 132 then d107 (change p 113 (some 112)) else d100 (change p 113 (some 112))) = d108 p
  rw [sub1420, sub1413]
  rfl
theorem sub1422 (p : Pattern) : d239 (change p 113 (some 112)) = d108 p := by
  change d108 (change p 113 (some 112)) = d108 p
  exact sub1421 p
theorem sub1423 (p : Pattern) : d240 (change p 113 (some 112)) = d108 p := by
  change d239 (change p 113 (some 112)) = d108 p
  exact sub1422 p
theorem sub1424 (p : Pattern) : d241 (change p 113 (some 112)) = d1127 p := by
  change (if p 106 then d240 (change p 113 (some 112)) else d237 (change p 113 (some 112))) = d1127 p
  rw [sub1423, sub1419]
  rfl
theorem sub1425 (p : Pattern) : d242 (change p 113 (some 112)) = d1128 p := by
  change (if p 86 then d241 (change p 113 (some 112)) else d234 (change p 113 (some 112))) = d1128 p
  rw [sub1424, sub1408]
  rfl
theorem sub1426 (p : Pattern) : d243 (change p 113 (some 112)) = d51 p := by
  change d51 (change p 113 (some 112)) = d51 p
  exact sub1398 p
theorem sub1427 (p : Pattern) : d244 (change p 113 (some 112)) = d51 p := by
  change d243 (change p 113 (some 112)) = d51 p
  exact sub1426 p
theorem sub1428 (p : Pattern) : d245 (change p 113 (some 112)) = d80 p := by
  change d80 (change p 113 (some 112)) = d80 p
  exact sub1405 p
theorem sub1429 (p : Pattern) : d246 (change p 113 (some 112)) = d80 p := by
  change d245 (change p 113 (some 112)) = d80 p
  exact sub1428 p
theorem sub1430 (p : Pattern) : d247 (change p 113 (some 112)) = d860 p := by
  change (if p 106 then d246 (change p 113 (some 112)) else d244 (change p 113 (some 112))) = d860 p
  rw [sub1429, sub1427]
  rfl
theorem sub1431 (p : Pattern) : d249 (change p 113 (some 112)) = d102 p := by
  change d102 (change p 113 (some 112)) = d102 p
  exact sub1417 p
theorem sub1432 (p : Pattern) : d250 (change p 113 (some 112)) = d102 p := by
  change d249 (change p 113 (some 112)) = d102 p
  exact sub1431 p
theorem sub1433 (p : Pattern) : d109 (change p 113 (some 112)) = d109 p := by
  change (if p 134 then d70 (change p 113 (some 112)) else d97 (change p 113 (some 112))) = d109 p
  rw [sub1402, sub1409]
  rfl
theorem sub1434 (p : Pattern) : d110 (change p 113 (some 112)) = d110 p := by
  change (if p 133 then d109 (change p 113 (some 112)) else d97 (change p 113 (some 112))) = d110 p
  rw [sub1433, sub1409]
  rfl
theorem sub1435 (p : Pattern) : d111 (change p 113 (some 112)) = d111 p := by
  change (if p 133 then d2 (change p 113 (some 112)) else d109 (change p 113 (some 112))) = d111 p
  rw [sub1358, sub1433]
  rfl
theorem sub1436 (p : Pattern) : d112 (change p 113 (some 112)) = d112 p := by
  change (if p 132 then d111 (change p 113 (some 112)) else d110 (change p 113 (some 112))) = d112 p
  rw [sub1435, sub1434]
  rfl
theorem sub1437 (p : Pattern) : d130 (change p 113 (some 112)) = d112 p := by
  change d112 (change p 113 (some 112)) = d112 p
  exact sub1436 p
theorem sub1438 (p : Pattern) : d252 (change p 113 (some 112)) = d112 p := by
  change d130 (change p 113 (some 112)) = d112 p
  exact sub1437 p
theorem sub1439 (p : Pattern) : d253 (change p 113 (some 112)) = d1129 p := by
  change (if p 106 then d252 (change p 113 (some 112)) else d250 (change p 113 (some 112))) = d1129 p
  rw [sub1438, sub1432]
  rfl
end NetHack.Sokoban32Refined
