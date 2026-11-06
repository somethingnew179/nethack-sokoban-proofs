/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1440 (p : Pattern) : d254 (change p 113 (some 112)) = d1130 p := by
  change (if p 86 then d253 (change p 113 (some 112)) else d247 (change p 113 (some 112))) = d1130 p
  rw [sub1439, sub1430]
  rfl
theorem sub1441 (p : Pattern) : d255 (change p 113 (some 112)) = d1131 p := by
  change (if p 80 then d254 (change p 113 (some 112)) else d242 (change p 113 (some 112))) = d1131 p
  rw [sub1440, sub1425]
  rfl
theorem sub1442 (p : Pattern) : d0 (change p 132 (some 133)) = d0 p := by
  rfl
theorem sub1443 (p : Pattern) : d2 (change p 132 (some 133)) = d2 p := by
  rfl
theorem sub1444 (p : Pattern) : d3 (change p 132 (some 133)) = d3 p := by
  change (if p 161 then d2 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d3 p
  rw [sub1443, sub1442]
  rfl
theorem sub1445 (p : Pattern) : d4 (change p 132 (some 133)) = d4 p := by
  change (if p 160 then d3 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d4 p
  rw [sub1444, sub1442]
  rfl
theorem sub1446 (p : Pattern) : d5 (change p 132 (some 133)) = d5 p := by
  change (if p 160 then d2 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d5 p
  rw [sub1443, sub1442]
  rfl
theorem sub1447 (p : Pattern) : d6 (change p 132 (some 133)) = d6 p := by
  change (if p 159 then d5 (change p 132 (some 133)) else d4 (change p 132 (some 133))) = d6 p
  rw [sub1446, sub1445]
  rfl
theorem sub1448 (p : Pattern) : d7 (change p 132 (some 133)) = d7 p := by
  change (if p 159 then d2 (change p 132 (some 133)) else d4 (change p 132 (some 133))) = d7 p
  rw [sub1443, sub1445]
  rfl
theorem sub1449 (p : Pattern) : d8 (change p 132 (some 133)) = d8 p := by
  change (if p 158 then d7 (change p 132 (some 133)) else d6 (change p 132 (some 133))) = d8 p
  rw [sub1448, sub1447]
  rfl
theorem sub1450 (p : Pattern) : d1 (change p 132 (some 133)) = d1 p := by
  rfl
theorem sub1451 (p : Pattern) : d9 (change p 132 (some 133)) = d9 p := by
  change (if p 161 then d2 (change p 132 (some 133)) else d1 (change p 132 (some 133))) = d9 p
  rw [sub1443, sub1450]
  rfl
theorem sub1452 (p : Pattern) : d10 (change p 132 (some 133)) = d10 p := by
  change (if p 160 then d9 (change p 132 (some 133)) else d1 (change p 132 (some 133))) = d10 p
  rw [sub1451, sub1450]
  rfl
theorem sub1453 (p : Pattern) : d11 (change p 132 (some 133)) = d11 p := by
  change (if p 160 then d2 (change p 132 (some 133)) else d1 (change p 132 (some 133))) = d11 p
  rw [sub1443, sub1450]
  rfl
theorem sub1454 (p : Pattern) : d12 (change p 132 (some 133)) = d12 p := by
  change (if p 159 then d11 (change p 132 (some 133)) else d10 (change p 132 (some 133))) = d12 p
  rw [sub1453, sub1452]
  rfl
theorem sub1455 (p : Pattern) : d13 (change p 132 (some 133)) = d13 p := by
  change (if p 159 then d2 (change p 132 (some 133)) else d10 (change p 132 (some 133))) = d13 p
  rw [sub1443, sub1452]
  rfl
theorem sub1456 (p : Pattern) : d14 (change p 132 (some 133)) = d14 p := by
  change (if p 158 then d13 (change p 132 (some 133)) else d12 (change p 132 (some 133))) = d14 p
  rw [sub1455, sub1454]
  rfl
theorem sub1457 (p : Pattern) : d15 (change p 132 (some 133)) = d15 p := by
  change (if p 139 then d14 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d15 p
  rw [sub1456, sub1449]
  rfl
theorem sub1458 (p : Pattern) : d16 (change p 132 (some 133)) = d16 p := by
  change (if p 138 then d15 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d16 p
  rw [sub1457, sub1449]
  rfl
theorem sub1459 (p : Pattern) : d17 (change p 132 (some 133)) = d17 p := by
  change (if p 160 then d2 (change p 132 (some 133)) else d3 (change p 132 (some 133))) = d17 p
  rw [sub1443, sub1444]
  rfl
theorem sub1460 (p : Pattern) : d18 (change p 132 (some 133)) = d18 p := by
  change (if p 159 then d17 (change p 132 (some 133)) else d4 (change p 132 (some 133))) = d18 p
  rw [sub1459, sub1445]
  rfl
theorem sub1461 (p : Pattern) : d19 (change p 132 (some 133)) = d19 p := by
  change (if p 159 then d2 (change p 132 (some 133)) else d17 (change p 132 (some 133))) = d19 p
  rw [sub1443, sub1459]
  rfl
theorem sub1462 (p : Pattern) : d20 (change p 132 (some 133)) = d20 p := by
  change (if p 158 then d19 (change p 132 (some 133)) else d18 (change p 132 (some 133))) = d20 p
  rw [sub1461, sub1460]
  rfl
theorem sub1463 (p : Pattern) : d21 (change p 132 (some 133)) = d21 p := by
  change (if p 160 then d2 (change p 132 (some 133)) else d9 (change p 132 (some 133))) = d21 p
  rw [sub1443, sub1451]
  rfl
theorem sub1464 (p : Pattern) : d22 (change p 132 (some 133)) = d22 p := by
  change (if p 159 then d21 (change p 132 (some 133)) else d10 (change p 132 (some 133))) = d22 p
  rw [sub1463, sub1452]
  rfl
theorem sub1465 (p : Pattern) : d23 (change p 132 (some 133)) = d23 p := by
  change (if p 159 then d2 (change p 132 (some 133)) else d21 (change p 132 (some 133))) = d23 p
  rw [sub1443, sub1463]
  rfl
theorem sub1466 (p : Pattern) : d24 (change p 132 (some 133)) = d24 p := by
  change (if p 158 then d23 (change p 132 (some 133)) else d22 (change p 132 (some 133))) = d24 p
  rw [sub1465, sub1464]
  rfl
theorem sub1467 (p : Pattern) : d25 (change p 132 (some 133)) = d25 p := by
  change (if p 139 then d24 (change p 132 (some 133)) else d20 (change p 132 (some 133))) = d25 p
  rw [sub1466, sub1462]
  rfl
theorem sub1468 (p : Pattern) : d26 (change p 132 (some 133)) = d26 p := by
  change (if p 138 then d25 (change p 132 (some 133)) else d20 (change p 132 (some 133))) = d26 p
  rw [sub1467, sub1462]
  rfl
theorem sub1469 (p : Pattern) : d27 (change p 132 (some 133)) = d27 p := by
  change (if p 134 then d26 (change p 132 (some 133)) else d16 (change p 132 (some 133))) = d27 p
  rw [sub1468, sub1458]
  rfl
theorem sub1470 (p : Pattern) : d28 (change p 132 (some 133)) = d27 p := by
  change d27 (change p 132 (some 133)) = d27 p
  exact sub1469 p
theorem sub1471 (p : Pattern) : d256 (change p 132 (some 133)) = d27 p := by
  change d28 (change p 132 (some 133)) = d27 p
  exact sub1470 p
theorem sub1472 (p : Pattern) : d46 (change p 132 (some 133)) = d46 p := by
  change (if p 134 then d25 (change p 132 (some 133)) else d15 (change p 132 (some 133))) = d46 p
  rw [sub1467, sub1457]
  rfl
theorem sub1473 (p : Pattern) : d47 (change p 132 (some 133)) = d46 p := by
  change d46 (change p 132 (some 133)) = d46 p
  exact sub1472 p
theorem sub1474 (p : Pattern) : d257 (change p 132 (some 133)) = d46 p := by
  change d47 (change p 132 (some 133)) = d46 p
  exact sub1473 p
theorem sub1475 (p : Pattern) : d52 (change p 132 (some 133)) = d52 p := by
  change (if p 139 then d2 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d52 p
  rw [sub1443, sub1449]
  rfl
theorem sub1476 (p : Pattern) : d53 (change p 132 (some 133)) = d53 p := by
  change (if p 138 then d52 (change p 132 (some 133)) else d15 (change p 132 (some 133))) = d53 p
  rw [sub1475, sub1457]
  rfl
theorem sub1477 (p : Pattern) : d54 (change p 132 (some 133)) = d54 p := by
  change (if p 139 then d2 (change p 132 (some 133)) else d20 (change p 132 (some 133))) = d54 p
  rw [sub1443, sub1462]
  rfl
theorem sub1478 (p : Pattern) : d55 (change p 132 (some 133)) = d55 p := by
  change (if p 138 then d54 (change p 132 (some 133)) else d25 (change p 132 (some 133))) = d55 p
  rw [sub1477, sub1467]
  rfl
theorem sub1479 (p : Pattern) : d56 (change p 132 (some 133)) = d56 p := by
  change (if p 134 then d55 (change p 132 (some 133)) else d53 (change p 132 (some 133))) = d56 p
  rw [sub1478, sub1476]
  rfl
theorem sub1480 (p : Pattern) : d57 (change p 132 (some 133)) = d56 p := by
  change d56 (change p 132 (some 133)) = d56 p
  exact sub1479 p
theorem sub1481 (p : Pattern) : d258 (change p 132 (some 133)) = d56 p := by
  change d57 (change p 132 (some 133)) = d56 p
  exact sub1480 p
theorem sub1482 (p : Pattern) : d259 (change p 132 (some 133)) = d1133 p := by
  change (if p 113 then d258 (change p 132 (some 133)) else d257 (change p 132 (some 133))) = d1133 p
  rw [sub1481, sub1474]
  rfl
theorem sub1483 (p : Pattern) : d260 (change p 132 (some 133)) = d1134 p := by
  change (if p 112 then d259 (change p 132 (some 133)) else d256 (change p 132 (some 133))) = d1134 p
  rw [sub1482, sub1471]
  rfl
theorem sub1484 (p : Pattern) : d261 (change p 132 (some 133)) = d27 p := by
  change d28 (change p 132 (some 133)) = d27 p
  exact sub1470 p
theorem sub1485 (p : Pattern) : d262 (change p 132 (some 133)) = d27 p := by
  change (if p 113 then d261 (change p 132 (some 133)) else d256 (change p 132 (some 133))) = d27 p
  rw [sub1484, sub1471]
  simp only [ite_self]
theorem sub1486 (p : Pattern) : d263 (change p 132 (some 133)) = d56 p := by
  change d57 (change p 132 (some 133)) = d56 p
  exact sub1480 p
theorem sub1487 (p : Pattern) : d264 (change p 132 (some 133)) = d1133 p := by
  change (if p 113 then d263 (change p 132 (some 133)) else d257 (change p 132 (some 133))) = d1133 p
  rw [sub1486, sub1474]
  rfl
theorem sub1488 (p : Pattern) : d265 (change p 132 (some 133)) = d1134 p := by
  change (if p 112 then d264 (change p 132 (some 133)) else d262 (change p 132 (some 133))) = d1134 p
  rw [sub1487, sub1485]
  rfl
theorem sub1489 (p : Pattern) : d266 (change p 132 (some 133)) = d1134 p := by
  change (if p 106 then d265 (change p 132 (some 133)) else d260 (change p 132 (some 133))) = d1134 p
  rw [sub1488, sub1483]
  simp only [ite_self]
theorem sub1490 (p : Pattern) : d86 (change p 132 (some 133)) = d86 p := by
  change (if p 138 then d52 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d86 p
  rw [sub1475, sub1449]
  rfl
theorem sub1491 (p : Pattern) : d87 (change p 132 (some 133)) = d87 p := by
  change (if p 138 then d54 (change p 132 (some 133)) else d20 (change p 132 (some 133))) = d87 p
  rw [sub1477, sub1462]
  rfl
theorem sub1492 (p : Pattern) : d88 (change p 132 (some 133)) = d88 p := by
  change (if p 134 then d87 (change p 132 (some 133)) else d86 (change p 132 (some 133))) = d88 p
  rw [sub1491, sub1490]
  rfl
theorem sub1493 (p : Pattern) : d89 (change p 132 (some 133)) = d88 p := by
  change d88 (change p 132 (some 133)) = d88 p
  exact sub1492 p
theorem sub1494 (p : Pattern) : d267 (change p 132 (some 133)) = d88 p := by
  change d89 (change p 132 (some 133)) = d88 p
  exact sub1493 p
theorem sub1495 (p : Pattern) : d268 (change p 132 (some 133)) = d1135 p := by
  change (if p 113 then d267 (change p 132 (some 133)) else d256 (change p 132 (some 133))) = d1135 p
  rw [sub1494, sub1471]
  rfl
theorem sub1496 (p : Pattern) : d97 (change p 132 (some 133)) = d97 p := by
  change (if p 139 then d2 (change p 132 (some 133)) else d14 (change p 132 (some 133))) = d97 p
  rw [sub1443, sub1456]
  rfl
theorem sub1497 (p : Pattern) : d98 (change p 132 (some 133)) = d98 p := by
  change (if p 138 then d97 (change p 132 (some 133)) else d14 (change p 132 (some 133))) = d98 p
  rw [sub1496, sub1456]
  rfl
theorem sub1498 (p : Pattern) : d70 (change p 132 (some 133)) = d70 p := by
  change (if p 139 then d2 (change p 132 (some 133)) else d24 (change p 132 (some 133))) = d70 p
  rw [sub1443, sub1466]
  rfl
theorem sub1499 (p : Pattern) : d71 (change p 132 (some 133)) = d71 p := by
  change (if p 138 then d70 (change p 132 (some 133)) else d24 (change p 132 (some 133))) = d71 p
  rw [sub1498, sub1466]
  rfl
theorem sub1500 (p : Pattern) : d99 (change p 132 (some 133)) = d99 p := by
  change (if p 134 then d71 (change p 132 (some 133)) else d98 (change p 132 (some 133))) = d99 p
  rw [sub1499, sub1497]
  rfl
theorem sub1501 (p : Pattern) : d100 (change p 132 (some 133)) = d99 p := by
  change d99 (change p 132 (some 133)) = d99 p
  exact sub1500 p
theorem sub1502 (p : Pattern) : d269 (change p 132 (some 133)) = d99 p := by
  change d100 (change p 132 (some 133)) = d99 p
  exact sub1501 p
theorem sub1503 (p : Pattern) : d270 (change p 132 (some 133)) = d99 p := by
  change d100 (change p 132 (some 133)) = d99 p
  exact sub1501 p
theorem sub1504 (p : Pattern) : d271 (change p 132 (some 133)) = d99 p := by
  change (if p 113 then d270 (change p 132 (some 133)) else d269 (change p 132 (some 133))) = d99 p
  rw [sub1503, sub1502]
  simp only [ite_self]
theorem sub1505 (p : Pattern) : d272 (change p 132 (some 133)) = d1136 p := by
  change (if p 112 then d271 (change p 132 (some 133)) else d268 (change p 132 (some 133))) = d1136 p
  rw [sub1504, sub1495]
  rfl
theorem sub1506 (p : Pattern) : d273 (change p 132 (some 133)) = d88 p := by
  change d89 (change p 132 (some 133)) = d88 p
  exact sub1493 p
theorem sub1507 (p : Pattern) : d274 (change p 132 (some 133)) = d1135 p := by
  change (if p 113 then d273 (change p 132 (some 133)) else d261 (change p 132 (some 133))) = d1135 p
  rw [sub1506, sub1484]
  rfl
theorem sub1508 (p : Pattern) : d109 (change p 132 (some 133)) = d109 p := by
  change (if p 134 then d70 (change p 132 (some 133)) else d97 (change p 132 (some 133))) = d109 p
  rw [sub1498, sub1496]
  rfl
theorem sub1509 (p : Pattern) : d110 (change p 132 (some 133)) = d109 p := by
  change d109 (change p 132 (some 133)) = d109 p
  exact sub1508 p
theorem sub1510 (p : Pattern) : d275 (change p 132 (some 133)) = d109 p := by
  change d110 (change p 132 (some 133)) = d109 p
  exact sub1509 p
theorem sub1511 (p : Pattern) : d276 (change p 132 (some 133)) = d1137 p := by
  change (if p 113 then d275 (change p 132 (some 133)) else d270 (change p 132 (some 133))) = d1137 p
  rw [sub1510, sub1503]
  rfl
theorem sub1512 (p : Pattern) : d277 (change p 132 (some 133)) = d1138 p := by
  change (if p 112 then d276 (change p 132 (some 133)) else d274 (change p 132 (some 133))) = d1138 p
  rw [sub1511, sub1507]
  rfl
theorem sub1513 (p : Pattern) : d278 (change p 132 (some 133)) = d1139 p := by
  change (if p 106 then d277 (change p 132 (some 133)) else d272 (change p 132 (some 133))) = d1139 p
  rw [sub1512, sub1505]
  rfl
theorem sub1514 (p : Pattern) : d279 (change p 132 (some 133)) = d1140 p := by
  change (if p 86 then d278 (change p 132 (some 133)) else d266 (change p 132 (some 133))) = d1140 p
  rw [sub1513, sub1489]
  rfl
theorem sub1515 (p : Pattern) : d280 (change p 132 (some 133)) = d27 p := by
  change d28 (change p 132 (some 133)) = d27 p
  exact sub1470 p
theorem sub1516 (p : Pattern) : d281 (change p 132 (some 133)) = d27 p := by
  change (if p 113 then d280 (change p 132 (some 133)) else d261 (change p 132 (some 133))) = d27 p
  rw [sub1515, sub1484]
  simp only [ite_self]
theorem sub1517 (p : Pattern) : d282 (change p 132 (some 133)) = d46 p := by
  change d47 (change p 132 (some 133)) = d46 p
  exact sub1473 p
theorem sub1518 (p : Pattern) : d283 (change p 132 (some 133)) = d56 p := by
  change d57 (change p 132 (some 133)) = d56 p
  exact sub1480 p
theorem sub1519 (p : Pattern) : d284 (change p 132 (some 133)) = d1133 p := by
  change (if p 113 then d283 (change p 132 (some 133)) else d282 (change p 132 (some 133))) = d1133 p
  rw [sub1518, sub1517]
  rfl
theorem sub1520 (p : Pattern) : d285 (change p 132 (some 133)) = d1134 p := by
  change (if p 112 then d284 (change p 132 (some 133)) else d281 (change p 132 (some 133))) = d1134 p
  rw [sub1519, sub1516]
  rfl
theorem sub1521 (p : Pattern) : d286 (change p 132 (some 133)) = d1134 p := by
  change (if p 106 then d285 (change p 132 (some 133)) else d265 (change p 132 (some 133))) = d1134 p
  rw [sub1520, sub1488]
  simp only [ite_self]
theorem sub1522 (p : Pattern) : d287 (change p 132 (some 133)) = d1141 p := by
  change (if p 113 then d283 (change p 132 (some 133)) else d280 (change p 132 (some 133))) = d1141 p
  rw [sub1518, sub1515]
  rfl
theorem sub1523 (p : Pattern) : d288 (change p 132 (some 133)) = d1142 p := by
  change (if p 113 then d2 (change p 132 (some 133)) else d275 (change p 132 (some 133))) = d1142 p
  rw [sub1443, sub1510]
  rfl
theorem sub1524 (p : Pattern) : d289 (change p 132 (some 133)) = d1143 p := by
  change (if p 112 then d288 (change p 132 (some 133)) else d287 (change p 132 (some 133))) = d1143 p
  rw [sub1523, sub1522]
  rfl
theorem sub1525 (p : Pattern) : d290 (change p 132 (some 133)) = d1144 p := by
  change (if p 106 then d289 (change p 132 (some 133)) else d277 (change p 132 (some 133))) = d1144 p
  rw [sub1524, sub1512]
  rfl
theorem sub1526 (p : Pattern) : d291 (change p 132 (some 133)) = d1145 p := by
  change (if p 86 then d290 (change p 132 (some 133)) else d286 (change p 132 (some 133))) = d1145 p
  rw [sub1525, sub1521]
  rfl
theorem sub1527 (p : Pattern) : d292 (change p 132 (some 133)) = d1146 p := by
  change (if p 80 then d291 (change p 132 (some 133)) else d279 (change p 132 (some 133))) = d1146 p
  rw [sub1526, sub1514]
  rfl
theorem sub1528 (p : Pattern) : d0 (change p 106 (some 80)) = d0 p := by
  rfl
theorem sub1529 (p : Pattern) : d2 (change p 106 (some 80)) = d2 p := by
  rfl
theorem sub1530 (p : Pattern) : d3 (change p 106 (some 80)) = d3 p := by
  change (if p 161 then d2 (change p 106 (some 80)) else d0 (change p 106 (some 80))) = d3 p
  rw [sub1529, sub1528]
  rfl
theorem sub1531 (p : Pattern) : d4 (change p 106 (some 80)) = d4 p := by
  change (if p 160 then d3 (change p 106 (some 80)) else d0 (change p 106 (some 80))) = d4 p
  rw [sub1530, sub1528]
  rfl
theorem sub1532 (p : Pattern) : d5 (change p 106 (some 80)) = d5 p := by
  change (if p 160 then d2 (change p 106 (some 80)) else d0 (change p 106 (some 80))) = d5 p
  rw [sub1529, sub1528]
  rfl
theorem sub1533 (p : Pattern) : d6 (change p 106 (some 80)) = d6 p := by
  change (if p 159 then d5 (change p 106 (some 80)) else d4 (change p 106 (some 80))) = d6 p
  rw [sub1532, sub1531]
  rfl
theorem sub1534 (p : Pattern) : d7 (change p 106 (some 80)) = d7 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d4 (change p 106 (some 80))) = d7 p
  rw [sub1529, sub1531]
  rfl
theorem sub1535 (p : Pattern) : d8 (change p 106 (some 80)) = d8 p := by
  change (if p 158 then d7 (change p 106 (some 80)) else d6 (change p 106 (some 80))) = d8 p
  rw [sub1534, sub1533]
  rfl
theorem sub1536 (p : Pattern) : d1 (change p 106 (some 80)) = d1 p := by
  rfl
theorem sub1537 (p : Pattern) : d9 (change p 106 (some 80)) = d9 p := by
  change (if p 161 then d2 (change p 106 (some 80)) else d1 (change p 106 (some 80))) = d9 p
  rw [sub1529, sub1536]
  rfl
theorem sub1538 (p : Pattern) : d10 (change p 106 (some 80)) = d10 p := by
  change (if p 160 then d9 (change p 106 (some 80)) else d1 (change p 106 (some 80))) = d10 p
  rw [sub1537, sub1536]
  rfl
theorem sub1539 (p : Pattern) : d11 (change p 106 (some 80)) = d11 p := by
  change (if p 160 then d2 (change p 106 (some 80)) else d1 (change p 106 (some 80))) = d11 p
  rw [sub1529, sub1536]
  rfl
theorem sub1540 (p : Pattern) : d12 (change p 106 (some 80)) = d12 p := by
  change (if p 159 then d11 (change p 106 (some 80)) else d10 (change p 106 (some 80))) = d12 p
  rw [sub1539, sub1538]
  rfl
theorem sub1541 (p : Pattern) : d13 (change p 106 (some 80)) = d13 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d10 (change p 106 (some 80))) = d13 p
  rw [sub1529, sub1538]
  rfl
theorem sub1542 (p : Pattern) : d14 (change p 106 (some 80)) = d14 p := by
  change (if p 158 then d13 (change p 106 (some 80)) else d12 (change p 106 (some 80))) = d14 p
  rw [sub1541, sub1540]
  rfl
theorem sub1543 (p : Pattern) : d15 (change p 106 (some 80)) = d15 p := by
  change (if p 139 then d14 (change p 106 (some 80)) else d8 (change p 106 (some 80))) = d15 p
  rw [sub1542, sub1535]
  rfl
theorem sub1544 (p : Pattern) : d16 (change p 106 (some 80)) = d16 p := by
  change (if p 138 then d15 (change p 106 (some 80)) else d8 (change p 106 (some 80))) = d16 p
  rw [sub1543, sub1535]
  rfl
theorem sub1545 (p : Pattern) : d17 (change p 106 (some 80)) = d17 p := by
  change (if p 160 then d2 (change p 106 (some 80)) else d3 (change p 106 (some 80))) = d17 p
  rw [sub1529, sub1530]
  rfl
theorem sub1546 (p : Pattern) : d18 (change p 106 (some 80)) = d18 p := by
  change (if p 159 then d17 (change p 106 (some 80)) else d4 (change p 106 (some 80))) = d18 p
  rw [sub1545, sub1531]
  rfl
theorem sub1547 (p : Pattern) : d19 (change p 106 (some 80)) = d19 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d17 (change p 106 (some 80))) = d19 p
  rw [sub1529, sub1545]
  rfl
theorem sub1548 (p : Pattern) : d20 (change p 106 (some 80)) = d20 p := by
  change (if p 158 then d19 (change p 106 (some 80)) else d18 (change p 106 (some 80))) = d20 p
  rw [sub1547, sub1546]
  rfl
theorem sub1549 (p : Pattern) : d21 (change p 106 (some 80)) = d21 p := by
  change (if p 160 then d2 (change p 106 (some 80)) else d9 (change p 106 (some 80))) = d21 p
  rw [sub1529, sub1537]
  rfl
theorem sub1550 (p : Pattern) : d22 (change p 106 (some 80)) = d22 p := by
  change (if p 159 then d21 (change p 106 (some 80)) else d10 (change p 106 (some 80))) = d22 p
  rw [sub1549, sub1538]
  rfl
theorem sub1551 (p : Pattern) : d23 (change p 106 (some 80)) = d23 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d21 (change p 106 (some 80))) = d23 p
  rw [sub1529, sub1549]
  rfl
theorem sub1552 (p : Pattern) : d24 (change p 106 (some 80)) = d24 p := by
  change (if p 158 then d23 (change p 106 (some 80)) else d22 (change p 106 (some 80))) = d24 p
  rw [sub1551, sub1550]
  rfl
theorem sub1553 (p : Pattern) : d25 (change p 106 (some 80)) = d25 p := by
  change (if p 139 then d24 (change p 106 (some 80)) else d20 (change p 106 (some 80))) = d25 p
  rw [sub1552, sub1548]
  rfl
theorem sub1554 (p : Pattern) : d26 (change p 106 (some 80)) = d26 p := by
  change (if p 138 then d25 (change p 106 (some 80)) else d20 (change p 106 (some 80))) = d26 p
  rw [sub1553, sub1548]
  rfl
theorem sub1555 (p : Pattern) : d27 (change p 106 (some 80)) = d27 p := by
  change (if p 134 then d26 (change p 106 (some 80)) else d16 (change p 106 (some 80))) = d27 p
  rw [sub1554, sub1544]
  rfl
theorem sub1556 (p : Pattern) : d28 (change p 106 (some 80)) = d28 p := by
  change (if p 133 then d27 (change p 106 (some 80)) else d16 (change p 106 (some 80))) = d28 p
  rw [sub1555, sub1544]
  rfl
theorem sub1557 (p : Pattern) : d29 (change p 106 (some 80)) = d29 p := by
  change (if p 161 then d1 (change p 106 (some 80)) else d0 (change p 106 (some 80))) = d29 p
  rw [sub1536, sub1528]
  rfl
theorem sub1558 (p : Pattern) : d30 (change p 106 (some 80)) = d30 p := by
  change (if p 160 then d2 (change p 106 (some 80)) else d29 (change p 106 (some 80))) = d30 p
  rw [sub1529, sub1557]
  rfl
theorem sub1559 (p : Pattern) : d31 (change p 106 (some 80)) = d31 p := by
  change (if p 159 then d30 (change p 106 (some 80)) else d4 (change p 106 (some 80))) = d31 p
  rw [sub1558, sub1531]
  rfl
end NetHack.Sokoban32Refined
