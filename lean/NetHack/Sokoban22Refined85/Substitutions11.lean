/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1320 (p : Pattern) : d28 (change p 10000 (some 49)) = d28 p := by
  change (if p 162 then d27 (change p 10000 (some 49)) else d21 (change p 10000 (some 49))) = d28 p
  rw [sub1319, sub1312]
  rfl
theorem sub1321 (p : Pattern) : d29 (change p 10000 (some 49)) = d29 p := by
  change (if p 161 then d28 (change p 10000 (some 49)) else d22 (change p 10000 (some 49))) = d29 p
  rw [sub1320, sub1313]
  rfl
theorem sub1322 (p : Pattern) : d2 (change p 10000 (some 49)) = d2 p := by
  rfl
theorem sub1323 (p : Pattern) : d30 (change p 10000 (some 49)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d2 (change p 10000 (some 49))) = d30 p
  rw [sub1302, sub1322]
  rfl
theorem sub1324 (p : Pattern) : d31 (change p 10000 (some 49)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 49)) else d2 (change p 10000 (some 49))) = d31 p
  rw [sub1323, sub1322]
  rfl
theorem sub1325 (p : Pattern) : d32 (change p 10000 (some 49)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d31 (change p 10000 (some 49))) = d32 p
  rw [sub1302, sub1324]
  rfl
theorem sub1326 (p : Pattern) : d33 (change p 10000 (some 49)) = d33 p := by
  change (if p 182 then d32 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d33 p
  rw [sub1325, sub1304]
  rfl
theorem sub1327 (p : Pattern) : d6 (change p 10000 (some 49)) = d6 p := by
  rfl
theorem sub1328 (p : Pattern) : d34 (change p 10000 (some 49)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d6 (change p 10000 (some 49))) = d34 p
  rw [sub1302, sub1327]
  rfl
theorem sub1329 (p : Pattern) : d35 (change p 10000 (some 49)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 49)) else d6 (change p 10000 (some 49))) = d35 p
  rw [sub1328, sub1327]
  rfl
theorem sub1330 (p : Pattern) : d36 (change p 10000 (some 49)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d35 (change p 10000 (some 49))) = d36 p
  rw [sub1302, sub1329]
  rfl
theorem sub1331 (p : Pattern) : d37 (change p 10000 (some 49)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d37 p
  rw [sub1330, sub1304]
  rfl
theorem sub1332 (p : Pattern) : d38 (change p 10000 (some 49)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 49)) else d33 (change p 10000 (some 49))) = d38 p
  rw [sub1331, sub1326]
  rfl
theorem sub1333 (p : Pattern) : d11 (change p 10000 (some 49)) = d11 p := by
  rfl
theorem sub1334 (p : Pattern) : d39 (change p 10000 (some 49)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d11 (change p 10000 (some 49))) = d39 p
  rw [sub1302, sub1333]
  rfl
theorem sub1335 (p : Pattern) : d40 (change p 10000 (some 49)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 49)) else d11 (change p 10000 (some 49))) = d40 p
  rw [sub1334, sub1333]
  rfl
theorem sub1336 (p : Pattern) : d41 (change p 10000 (some 49)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d40 (change p 10000 (some 49))) = d41 p
  rw [sub1302, sub1335]
  rfl
theorem sub1337 (p : Pattern) : d42 (change p 10000 (some 49)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d42 p
  rw [sub1336, sub1304]
  rfl
theorem sub1338 (p : Pattern) : d43 (change p 10000 (some 49)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d18 (change p 10000 (some 49))) = d43 p
  rw [sub1302, sub1309]
  rfl
theorem sub1339 (p : Pattern) : d44 (change p 10000 (some 49)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 49)) else d42 (change p 10000 (some 49))) = d44 p
  rw [sub1338, sub1337]
  rfl
theorem sub1340 (p : Pattern) : d45 (change p 10000 (some 49)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 49)) else d38 (change p 10000 (some 49))) = d45 p
  rw [sub1339, sub1332]
  rfl
theorem sub1341 (p : Pattern) : d46 (change p 10000 (some 49)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d46 p
  rw [sub1302, sub1304]
  rfl
theorem sub1342 (p : Pattern) : d47 (change p 10000 (some 49)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 49)) else d46 (change p 10000 (some 49))) = d47 p
  rw [sub1338, sub1341]
  rfl
theorem sub1343 (p : Pattern) : d48 (change p 10000 (some 49)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d24 (change p 10000 (some 49))) = d48 p
  rw [sub1302, sub1316]
  rfl
theorem sub1344 (p : Pattern) : d49 (change p 10000 (some 49)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d48 (change p 10000 (some 49))) = d49 p
  rw [sub1302, sub1343]
  rfl
theorem sub1345 (p : Pattern) : d50 (change p 10000 (some 49)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 49)) else d47 (change p 10000 (some 49))) = d50 p
  rw [sub1344, sub1342]
  rfl
theorem sub1346 (p : Pattern) : d51 (change p 10000 (some 49)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 49)) else d45 (change p 10000 (some 49))) = d51 p
  rw [sub1345, sub1340]
  rfl
theorem sub1347 (p : Pattern) : d52 (change p 10000 (some 49)) = d52 p := by
  change (if p 160 then d51 (change p 10000 (some 49)) else d29 (change p 10000 (some 49))) = d52 p
  rw [sub1346, sub1321]
  rfl
theorem sub1348 (p : Pattern) : d53 (change p 10000 (some 49)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 49)) else d31 (change p 10000 (some 49))) = d53 p
  rw [sub1325, sub1324]
  rfl
theorem sub1349 (p : Pattern) : d54 (change p 10000 (some 49)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 49)) else d16 (change p 10000 (some 49))) = d54 p
  rw [sub1348, sub1306]
  rfl
theorem sub1350 (p : Pattern) : d55 (change p 10000 (some 49)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 49)) else d20 (change p 10000 (some 49))) = d55 p
  rw [sub1318, sub1311]
  rfl
theorem sub1351 (p : Pattern) : d56 (change p 10000 (some 49)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 49)) else d54 (change p 10000 (some 49))) = d56 p
  rw [sub1350, sub1349]
  rfl
theorem sub1352 (p : Pattern) : d10 (change p 10000 (some 49)) = d10 p := by
  rfl
theorem sub1353 (p : Pattern) : d57 (change p 10000 (some 49)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d10 (change p 10000 (some 49))) = d57 p
  rw [sub1302, sub1352]
  rfl
theorem sub1354 (p : Pattern) : d58 (change p 10000 (some 49)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 49)) else d10 (change p 10000 (some 49))) = d58 p
  rw [sub1353, sub1352]
  rfl
theorem sub1355 (p : Pattern) : d59 (change p 10000 (some 49)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d58 (change p 10000 (some 49))) = d59 p
  rw [sub1302, sub1354]
  rfl
theorem sub1356 (p : Pattern) : d60 (change p 10000 (some 49)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 49)) else d58 (change p 10000 (some 49))) = d60 p
  rw [sub1355, sub1354]
  rfl
theorem sub1357 (p : Pattern) : d61 (change p 10000 (some 49)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 49)) else d20 (change p 10000 (some 49))) = d61 p
  rw [sub1356, sub1311]
  rfl
theorem sub1358 (p : Pattern) : d62 (change p 10000 (some 49)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 49)) else d40 (change p 10000 (some 49))) = d62 p
  rw [sub1336, sub1335]
  rfl
theorem sub1359 (p : Pattern) : d63 (change p 10000 (some 49)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d62 (change p 10000 (some 49))) = d63 p
  rw [sub1302, sub1358]
  rfl
theorem sub1360 (p : Pattern) : d64 (change p 10000 (some 49)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 49)) else d61 (change p 10000 (some 49))) = d64 p
  rw [sub1359, sub1357]
  rfl
theorem sub1361 (p : Pattern) : d65 (change p 10000 (some 49)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 49)) else d56 (change p 10000 (some 49))) = d65 p
  rw [sub1360, sub1351]
  rfl
theorem sub1362 (p : Pattern) : d66 (change p 10000 (some 49)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d31 (change p 10000 (some 49))) = d66 p
  rw [sub1302, sub1324]
  rfl
theorem sub1363 (p : Pattern) : d67 (change p 10000 (some 49)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 49)) else d37 (change p 10000 (some 49))) = d67 p
  rw [sub1362, sub1331]
  rfl
theorem sub1364 (p : Pattern) : d68 (change p 10000 (some 49)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 49)) else d43 (change p 10000 (some 49))) = d68 p
  rw [sub1343, sub1338]
  rfl
theorem sub1365 (p : Pattern) : d69 (change p 10000 (some 49)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 49)) else d67 (change p 10000 (some 49))) = d69 p
  rw [sub1364, sub1363]
  rfl
theorem sub1366 (p : Pattern) : d70 (change p 10000 (some 49)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d58 (change p 10000 (some 49))) = d70 p
  rw [sub1302, sub1354]
  rfl
theorem sub1367 (p : Pattern) : d71 (change p 10000 (some 49)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 49)) else d43 (change p 10000 (some 49))) = d71 p
  rw [sub1366, sub1338]
  rfl
theorem sub1368 (p : Pattern) : d72 (change p 10000 (some 49)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d40 (change p 10000 (some 49))) = d72 p
  rw [sub1302, sub1335]
  rfl
theorem sub1369 (p : Pattern) : d73 (change p 10000 (some 49)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d72 (change p 10000 (some 49))) = d73 p
  rw [sub1302, sub1368]
  rfl
theorem sub1370 (p : Pattern) : d74 (change p 10000 (some 49)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 49)) else d71 (change p 10000 (some 49))) = d74 p
  rw [sub1369, sub1367]
  rfl
theorem sub1371 (p : Pattern) : d75 (change p 10000 (some 49)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 49)) else d69 (change p 10000 (some 49))) = d75 p
  rw [sub1370, sub1365]
  rfl
theorem sub1372 (p : Pattern) : d76 (change p 10000 (some 49)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 49)) else d65 (change p 10000 (some 49))) = d76 p
  rw [sub1371, sub1361]
  rfl
theorem sub1373 (p : Pattern) : d77 (change p 10000 (some 49)) = d77 p := by
  change (if p 141 then d76 (change p 10000 (some 49)) else d52 (change p 10000 (some 49))) = d77 p
  rw [sub1372, sub1347]
  rfl
theorem sub1374 (p : Pattern) : d78 (change p 10000 (some 49)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 49)) else d35 (change p 10000 (some 49))) = d78 p
  rw [sub1330, sub1329]
  rfl
theorem sub1375 (p : Pattern) : d79 (change p 10000 (some 49)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 49)) else d53 (change p 10000 (some 49))) = d79 p
  rw [sub1374, sub1348]
  rfl
theorem sub1376 (p : Pattern) : d80 (change p 10000 (some 49)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 49)) else d79 (change p 10000 (some 49))) = d80 p
  rw [sub1359, sub1375]
  rfl
theorem sub1377 (p : Pattern) : d81 (change p 10000 (some 49)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 49)) else d80 (change p 10000 (some 49))) = d81 p
  rw [sub1302, sub1376]
  rfl
theorem sub1378 (p : Pattern) : d82 (change p 10000 (some 49)) = d82 p := by
  change (if p 160 then d81 (change p 10000 (some 49)) else d29 (change p 10000 (some 49))) = d82 p
  rw [sub1377, sub1321]
  rfl
theorem sub1379 (p : Pattern) : d83 (change p 10000 (some 49)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d78 (change p 10000 (some 49))) = d83 p
  rw [sub1302, sub1374]
  rfl
theorem sub1380 (p : Pattern) : d84 (change p 10000 (some 49)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 49)) else d83 (change p 10000 (some 49))) = d84 p
  rw [sub1302, sub1379]
  rfl
theorem sub1381 (p : Pattern) : d85 (change p 10000 (some 49)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 49)) else d84 (change p 10000 (some 49))) = d85 p
  rw [sub1302, sub1380]
  rfl
theorem sub1382 (p : Pattern) : d86 (change p 10000 (some 49)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 49)) else d65 (change p 10000 (some 49))) = d86 p
  rw [sub1381, sub1361]
  rfl
theorem sub1383 (p : Pattern) : d87 (change p 10000 (some 49)) = d87 p := by
  change (if p 141 then d86 (change p 10000 (some 49)) else d82 (change p 10000 (some 49))) = d87 p
  rw [sub1382, sub1378]
  rfl
theorem sub1384 (p : Pattern) : d88 (change p 10000 (some 49)) = d88 p := by
  change (if p 138 then d87 (change p 10000 (some 49)) else d77 (change p 10000 (some 49))) = d88 p
  rw [sub1383, sub1373]
  rfl
theorem sub1385 (p : Pattern) : d89 (change p 10000 (some 49)) = d89 p := by
  change (if p 163 then d62 (change p 10000 (some 49)) else d26 (change p 10000 (some 49))) = d89 p
  rw [sub1358, sub1318]
  rfl
theorem sub1386 (p : Pattern) : d90 (change p 10000 (some 49)) = d90 p := by
  change (if p 162 then d63 (change p 10000 (some 49)) else d89 (change p 10000 (some 49))) = d90 p
  rw [sub1359, sub1385]
  rfl
theorem sub1387 (p : Pattern) : d91 (change p 10000 (some 49)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 49)) else d63 (change p 10000 (some 49))) = d91 p
  rw [sub1302, sub1359]
  rfl
theorem sub1388 (p : Pattern) : d92 (change p 10000 (some 49)) = d92 p := by
  change (if p 161 then d91 (change p 10000 (some 49)) else d90 (change p 10000 (some 49))) = d92 p
  rw [sub1387, sub1386]
  rfl
theorem sub1389 (p : Pattern) : d93 (change p 10000 (some 49)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 49)) else d91 (change p 10000 (some 49))) = d93 p
  rw [sub1302, sub1387]
  rfl
theorem sub1390 (p : Pattern) : d94 (change p 10000 (some 49)) = d94 p := by
  change (if p 160 then d93 (change p 10000 (some 49)) else d92 (change p 10000 (some 49))) = d94 p
  rw [sub1389, sub1388]
  rfl
theorem sub1391 (p : Pattern) : d95 (change p 10000 (some 49)) = d95 p := by
  change (if p 160 then d12 (change p 10000 (some 49)) else d93 (change p 10000 (some 49))) = d95 p
  rw [sub1302, sub1389]
  rfl
theorem sub1392 (p : Pattern) : d96 (change p 10000 (some 49)) = d96 p := by
  change (if p 141 then d95 (change p 10000 (some 49)) else d94 (change p 10000 (some 49))) = d96 p
  rw [sub1391, sub1390]
  rfl
theorem sub1393 (p : Pattern) : d97 (change p 10000 (some 49)) = d97 p := by
  change (if p 138 then d96 (change p 10000 (some 49)) else d87 (change p 10000 (some 49))) = d97 p
  rw [sub1392, sub1383]
  rfl
theorem sub1394 (p : Pattern) : d98 (change p 10000 (some 49)) = d98 p := by
  change (if p 116 then d97 (change p 10000 (some 49)) else d88 (change p 10000 (some 49))) = d98 p
  rw [sub1393, sub1384]
  rfl
theorem sub1395 (p : Pattern) : d99 (change p 10000 (some 49)) = d99 p := by
  change (if p 138 then d12 (change p 10000 (some 49)) else d87 (change p 10000 (some 49))) = d99 p
  rw [sub1302, sub1383]
  rfl
theorem sub1396 (p : Pattern) : d100 (change p 10000 (some 49)) = d100 p := by
  change (if p 116 then d99 (change p 10000 (some 49)) else d88 (change p 10000 (some 49))) = d100 p
  rw [sub1395, sub1384]
  rfl
theorem sub1397 (p : Pattern) : d101 (change p 10000 (some 49)) = d101 p := by
  change (if p 115 then d100 (change p 10000 (some 49)) else d98 (change p 10000 (some 49))) = d101 p
  rw [sub1396, sub1394]
  rfl
theorem sub1398 (p : Pattern) : d1 (change p 10000 (some 49)) = d1 p := by
  rfl
theorem sub1399 (p : Pattern) : d102 (change p 10000 (some 49)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d1 (change p 10000 (some 49))) = d102 p
  rw [sub1302, sub1398]
  rfl
theorem sub1400 (p : Pattern) : d103 (change p 10000 (some 49)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 49)) else d1 (change p 10000 (some 49))) = d103 p
  rw [sub1399, sub1398]
  rfl
theorem sub1401 (p : Pattern) : d104 (change p 10000 (some 49)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d103 (change p 10000 (some 49))) = d104 p
  rw [sub1302, sub1400]
  rfl
theorem sub1402 (p : Pattern) : d105 (change p 10000 (some 49)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 49)) else d103 (change p 10000 (some 49))) = d105 p
  rw [sub1401, sub1400]
  rfl
theorem sub1403 (p : Pattern) : d5 (change p 10000 (some 49)) = d5 p := by
  rfl
theorem sub1404 (p : Pattern) : d106 (change p 10000 (some 49)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d5 (change p 10000 (some 49))) = d106 p
  rw [sub1302, sub1403]
  rfl
theorem sub1405 (p : Pattern) : d107 (change p 10000 (some 49)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 49)) else d5 (change p 10000 (some 49))) = d107 p
  rw [sub1404, sub1403]
  rfl
theorem sub1406 (p : Pattern) : d108 (change p 10000 (some 49)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d107 (change p 10000 (some 49))) = d108 p
  rw [sub1302, sub1405]
  rfl
theorem sub1407 (p : Pattern) : d109 (change p 10000 (some 49)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 49)) else d107 (change p 10000 (some 49))) = d109 p
  rw [sub1406, sub1405]
  rfl
theorem sub1408 (p : Pattern) : d110 (change p 10000 (some 49)) = d110 p := by
  change (if p 163 then d109 (change p 10000 (some 49)) else d105 (change p 10000 (some 49))) = d110 p
  rw [sub1407, sub1402]
  rfl
theorem sub1409 (p : Pattern) : d111 (change p 10000 (some 49)) = d111 p := by
  change (if p 162 then d110 (change p 10000 (some 49)) else d105 (change p 10000 (some 49))) = d111 p
  rw [sub1408, sub1402]
  rfl
theorem sub1410 (p : Pattern) : d112 (change p 10000 (some 49)) = d112 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d60 (change p 10000 (some 49))) = d112 p
  rw [sub1302, sub1356]
  rfl
theorem sub1411 (p : Pattern) : d113 (change p 10000 (some 49)) = d113 p := by
  change (if p 162 then d112 (change p 10000 (some 49)) else d110 (change p 10000 (some 49))) = d113 p
  rw [sub1410, sub1408]
  rfl
theorem sub1412 (p : Pattern) : d114 (change p 10000 (some 49)) = d114 p := by
  change (if p 161 then d113 (change p 10000 (some 49)) else d111 (change p 10000 (some 49))) = d114 p
  rw [sub1411, sub1409]
  rfl
theorem sub1413 (p : Pattern) : d3 (change p 10000 (some 49)) = d3 p := by
  rfl
theorem sub1414 (p : Pattern) : d115 (change p 10000 (some 49)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d3 (change p 10000 (some 49))) = d115 p
  rw [sub1302, sub1413]
  rfl
theorem sub1415 (p : Pattern) : d116 (change p 10000 (some 49)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 49)) else d3 (change p 10000 (some 49))) = d116 p
  rw [sub1414, sub1413]
  rfl
theorem sub1416 (p : Pattern) : d117 (change p 10000 (some 49)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d116 (change p 10000 (some 49))) = d117 p
  rw [sub1302, sub1415]
  rfl
theorem sub1417 (p : Pattern) : d118 (change p 10000 (some 49)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 49)) else d103 (change p 10000 (some 49))) = d118 p
  rw [sub1416, sub1400]
  rfl
theorem sub1418 (p : Pattern) : d7 (change p 10000 (some 49)) = d7 p := by
  rfl
theorem sub1419 (p : Pattern) : d119 (change p 10000 (some 49)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d7 (change p 10000 (some 49))) = d119 p
  rw [sub1302, sub1418]
  rfl
theorem sub1420 (p : Pattern) : d120 (change p 10000 (some 49)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 49)) else d7 (change p 10000 (some 49))) = d120 p
  rw [sub1419, sub1418]
  rfl
theorem sub1421 (p : Pattern) : d121 (change p 10000 (some 49)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d120 (change p 10000 (some 49))) = d121 p
  rw [sub1302, sub1420]
  rfl
theorem sub1422 (p : Pattern) : d122 (change p 10000 (some 49)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 49)) else d103 (change p 10000 (some 49))) = d122 p
  rw [sub1421, sub1400]
  rfl
theorem sub1423 (p : Pattern) : d123 (change p 10000 (some 49)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 49)) else d118 (change p 10000 (some 49))) = d123 p
  rw [sub1422, sub1417]
  rfl
theorem sub1424 (p : Pattern) : d124 (change p 10000 (some 49)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d103 (change p 10000 (some 49))) = d124 p
  rw [sub1302, sub1400]
  rfl
theorem sub1425 (p : Pattern) : d125 (change p 10000 (some 49)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d107 (change p 10000 (some 49))) = d125 p
  rw [sub1302, sub1405]
  rfl
theorem sub1426 (p : Pattern) : d126 (change p 10000 (some 49)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 49)) else d124 (change p 10000 (some 49))) = d126 p
  rw [sub1425, sub1424]
  rfl
theorem sub1427 (p : Pattern) : d127 (change p 10000 (some 49)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 49)) else d123 (change p 10000 (some 49))) = d127 p
  rw [sub1426, sub1423]
  rfl
theorem sub1428 (p : Pattern) : d128 (change p 10000 (some 49)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d70 (change p 10000 (some 49))) = d128 p
  rw [sub1302, sub1366]
  rfl
theorem sub1429 (p : Pattern) : d129 (change p 10000 (some 49)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 49)) else d126 (change p 10000 (some 49))) = d129 p
  rw [sub1428, sub1426]
  rfl
theorem sub1430 (p : Pattern) : d130 (change p 10000 (some 49)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 49)) else d127 (change p 10000 (some 49))) = d130 p
  rw [sub1429, sub1427]
  rfl
theorem sub1431 (p : Pattern) : d131 (change p 10000 (some 49)) = d131 p := by
  change (if p 160 then d130 (change p 10000 (some 49)) else d114 (change p 10000 (some 49))) = d131 p
  rw [sub1430, sub1412]
  rfl
theorem sub1432 (p : Pattern) : d132 (change p 10000 (some 49)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 49)) else d116 (change p 10000 (some 49))) = d132 p
  rw [sub1416, sub1415]
  rfl
theorem sub1433 (p : Pattern) : d133 (change p 10000 (some 49)) = d133 p := by
  change (if p 163 then d132 (change p 10000 (some 49)) else d105 (change p 10000 (some 49))) = d133 p
  rw [sub1432, sub1402]
  rfl
theorem sub1434 (p : Pattern) : d134 (change p 10000 (some 49)) = d134 p := by
  change (if p 163 then d60 (change p 10000 (some 49)) else d109 (change p 10000 (some 49))) = d134 p
  rw [sub1356, sub1407]
  rfl
theorem sub1435 (p : Pattern) : d135 (change p 10000 (some 49)) = d135 p := by
  change (if p 162 then d134 (change p 10000 (some 49)) else d133 (change p 10000 (some 49))) = d135 p
  rw [sub1434, sub1433]
  rfl
theorem sub1436 (p : Pattern) : d136 (change p 10000 (some 49)) = d136 p := by
  change (if p 163 then d62 (change p 10000 (some 49)) else d109 (change p 10000 (some 49))) = d136 p
  rw [sub1358, sub1407]
  rfl
theorem sub1437 (p : Pattern) : d137 (change p 10000 (some 49)) = d137 p := by
  change (if p 162 then d12 (change p 10000 (some 49)) else d136 (change p 10000 (some 49))) = d137 p
  rw [sub1302, sub1436]
  rfl
theorem sub1438 (p : Pattern) : d138 (change p 10000 (some 49)) = d138 p := by
  change (if p 161 then d137 (change p 10000 (some 49)) else d135 (change p 10000 (some 49))) = d138 p
  rw [sub1437, sub1435]
  rfl
theorem sub1439 (p : Pattern) : d139 (change p 10000 (some 49)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 49)) else d116 (change p 10000 (some 49))) = d139 p
  rw [sub1302, sub1415]
  rfl
end NetHack.Sokoban22Refined85
