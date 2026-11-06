/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1440 (p : Pattern) : d116 (change p 159 (some 158)) = d63 p := by
  change d63 (change p 159 (some 158)) = d63 p
  exact sub1439 p
theorem sub1441 (p : Pattern) : d335 (change p 159 (some 158)) = d64 p := by
  change (if p 141 then d116 (change p 159 (some 158)) else d114 (change p 159 (some 158))) = d64 p
  rw [sub1440, sub1425]
  rfl
theorem sub1442 (p : Pattern) : d106 (change p 159 (some 158)) = d106 p := by
  change (if p 160 then d55 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d106 p
  rw [sub1422, sub1419]
  rfl
theorem sub1443 (p : Pattern) : d107 (change p 159 (some 158)) = d106 p := by
  change d106 (change p 159 (some 158)) = d106 p
  exact sub1442 p
theorem sub1444 (p : Pattern) : d65 (change p 159 (some 158)) = d65 p := by
  change (if p 168 then d60 (change p 159 (some 158)) else d55 (change p 159 (some 158))) = d65 p
  rw [sub1436, sub1422]
  rfl
theorem sub1445 (p : Pattern) : d109 (change p 159 (some 158)) = d109 p := by
  change (if p 160 then d65 (change p 159 (some 158)) else d12 (change p 159 (some 158))) = d109 p
  rw [sub1444, sub1432]
  rfl
theorem sub1446 (p : Pattern) : d110 (change p 159 (some 158)) = d109 p := by
  change d109 (change p 159 (some 158)) = d109 p
  exact sub1445 p
theorem sub1447 (p : Pattern) : d336 (change p 159 (some 158)) = d227 p := by
  change (if p 141 then d110 (change p 159 (some 158)) else d107 (change p 159 (some 158))) = d227 p
  rw [sub1446, sub1443]
  rfl
theorem sub1448 (p : Pattern) : d337 (change p 159 (some 158)) = d228 p := by
  change (if p 134 then d336 (change p 159 (some 158)) else d335 (change p 159 (some 158))) = d228 p
  rw [sub1447, sub1441]
  rfl
theorem sub1449 (p : Pattern) : d338 (change p 159 (some 158)) = d55 p := by
  change d55 (change p 159 (some 158)) = d55 p
  exact sub1422 p
theorem sub1450 (p : Pattern) : d339 (change p 159 (some 158)) = d65 p := by
  change d65 (change p 159 (some 158)) = d65 p
  exact sub1444 p
theorem sub1451 (p : Pattern) : d340 (change p 159 (some 158)) = d66 p := by
  change (if p 141 then d339 (change p 159 (some 158)) else d338 (change p 159 (some 158))) = d66 p
  rw [sub1450, sub1449]
  rfl
theorem sub1452 (p : Pattern) : d211 (change p 159 (some 158)) = d55 p := by
  change d55 (change p 159 (some 158)) = d55 p
  exact sub1422 p
theorem sub1453 (p : Pattern) : d212 (change p 159 (some 158)) = d65 p := by
  change d65 (change p 159 (some 158)) = d65 p
  exact sub1444 p
theorem sub1454 (p : Pattern) : d213 (change p 159 (some 158)) = d66 p := by
  change (if p 141 then d212 (change p 159 (some 158)) else d211 (change p 159 (some 158))) = d66 p
  rw [sub1453, sub1452]
  rfl
theorem sub1455 (p : Pattern) : d341 (change p 159 (some 158)) = d66 p := by
  change (if p 134 then d213 (change p 159 (some 158)) else d340 (change p 159 (some 158))) = d66 p
  rw [sub1454, sub1451]
  simp only [ite_self]
theorem sub1456 (p : Pattern) : d342 (change p 159 (some 158)) = d1043 p := by
  change (if p 133 then d341 (change p 159 (some 158)) else d337 (change p 159 (some 158))) = d1043 p
  rw [sub1455, sub1448]
  rfl
theorem sub1457 (p : Pattern) : d66 (change p 159 (some 158)) = d66 p := by
  change (if p 141 then d65 (change p 159 (some 158)) else d55 (change p 159 (some 158))) = d66 p
  rw [sub1444, sub1422]
  rfl
theorem sub1458 (p : Pattern) : d343 (change p 159 (some 158)) = d66 p := by
  change (if p 133 then d66 (change p 159 (some 158)) else d341 (change p 159 (some 158))) = d66 p
  rw [sub1457, sub1455]
  simp only [ite_self]
theorem sub1459 (p : Pattern) : d344 (change p 159 (some 158)) = d1044 p := by
  change (if p 132 then d343 (change p 159 (some 158)) else d342 (change p 159 (some 158))) = d1044 p
  rw [sub1458, sub1456]
  rfl
theorem sub1460 (p : Pattern) : d345 (change p 159 (some 158)) = d67 p := by
  change (if p 134 then d66 (change p 159 (some 158)) else d335 (change p 159 (some 158))) = d67 p
  rw [sub1457, sub1441]
  rfl
theorem sub1461 (p : Pattern) : d347 (change p 159 (some 158)) = d55 p := by
  change d55 (change p 159 (some 158)) = d55 p
  exact sub1422 p
theorem sub1462 (p : Pattern) : d349 (change p 159 (some 158)) = d65 p := by
  change d65 (change p 159 (some 158)) = d65 p
  exact sub1444 p
theorem sub1463 (p : Pattern) : d350 (change p 159 (some 158)) = d66 p := by
  change (if p 141 then d349 (change p 159 (some 158)) else d347 (change p 159 (some 158))) = d66 p
  rw [sub1462, sub1461]
  rfl
theorem sub1464 (p : Pattern) : d351 (change p 159 (some 158)) = d66 p := by
  change (if p 134 then d66 (change p 159 (some 158)) else d350 (change p 159 (some 158))) = d66 p
  rw [sub1457, sub1463]
  simp only [ite_self]
theorem sub1465 (p : Pattern) : d352 (change p 159 (some 158)) = d217 p := by
  change (if p 133 then d351 (change p 159 (some 158)) else d345 (change p 159 (some 158))) = d217 p
  rw [sub1464, sub1460]
  rfl
theorem sub1466 (p : Pattern) : d353 (change p 159 (some 158)) = d66 p := by
  change (if p 134 then d66 (change p 159 (some 158)) else d340 (change p 159 (some 158))) = d66 p
  rw [sub1457, sub1451]
  simp only [ite_self]
theorem sub1467 (p : Pattern) : d354 (change p 159 (some 158)) = d66 p := by
  change (if p 133 then d66 (change p 159 (some 158)) else d353 (change p 159 (some 158))) = d66 p
  rw [sub1457, sub1466]
  simp only [ite_self]
theorem sub1468 (p : Pattern) : d355 (change p 159 (some 158)) = d1045 p := by
  change (if p 132 then d354 (change p 159 (some 158)) else d352 (change p 159 (some 158))) = d1045 p
  rw [sub1467, sub1465]
  rfl
theorem sub1469 (p : Pattern) : d356 (change p 159 (some 158)) = d1046 p := by
  change (if p 108 then d355 (change p 159 (some 158)) else d344 (change p 159 (some 158))) = d1046 p
  rw [sub1468, sub1459]
  rfl
theorem sub1470 (p : Pattern) : d0 (change p 187 none) = d0 p := by
  rfl
theorem sub1471 (p : Pattern) : d2 (change p 187 none) = d2 p := by
  rfl
theorem sub1472 (p : Pattern) : d6 (change p 187 none) = d6 p := by
  change (if p 193 then d2 (change p 187 none) else d0 (change p 187 none)) = d6 p
  rw [sub1471, sub1470]
  rfl
theorem sub1473 (p : Pattern) : d7 (change p 187 none) = d7 p := by
  change (if p 192 then d6 (change p 187 none) else d0 (change p 187 none)) = d7 p
  rw [sub1472, sub1470]
  rfl
theorem sub1474 (p : Pattern) : d119 (change p 187 none) = d7 p := by
  change d7 (change p 187 none) = d7 p
  exact sub1473 p
theorem sub1475 (p : Pattern) : d4 (change p 187 none) = d4 p := by
  rfl
theorem sub1476 (p : Pattern) : d54 (change p 187 none) = d54 p := by
  change (if p 193 then d4 (change p 187 none) else d2 (change p 187 none)) = d54 p
  rw [sub1475, sub1471]
  rfl
theorem sub1477 (p : Pattern) : d55 (change p 187 none) = d55 p := by
  change (if p 192 then d54 (change p 187 none) else d2 (change p 187 none)) = d55 p
  rw [sub1476, sub1471]
  rfl
theorem sub1478 (p : Pattern) : d137 (change p 187 none) = d56 p := by
  change (if p 186 then d55 (change p 187 none) else d119 (change p 187 none)) = d56 p
  rw [sub1477, sub1474]
  rfl
theorem sub1479 (p : Pattern) : d501 (change p 187 none) = d57 p := by
  change (if p 160 then d137 (change p 187 none) else d119 (change p 187 none)) = d57 p
  rw [sub1478, sub1474]
  rfl
theorem sub1480 (p : Pattern) : d1 (change p 187 none) = d1 p := by
  rfl
theorem sub1481 (p : Pattern) : d8 (change p 187 none) = d8 p := by
  change (if p 271 then d1 (change p 187 none) else d0 (change p 187 none)) = d8 p
  rw [sub1480, sub1470]
  rfl
theorem sub1482 (p : Pattern) : d3 (change p 187 none) = d3 p := by
  rfl
theorem sub1483 (p : Pattern) : d9 (change p 187 none) = d9 p := by
  change (if p 271 then d3 (change p 187 none) else d2 (change p 187 none)) = d9 p
  rw [sub1482, sub1471]
  rfl
theorem sub1484 (p : Pattern) : d10 (change p 187 none) = d10 p := by
  change (if p 193 then d9 (change p 187 none) else d8 (change p 187 none)) = d10 p
  rw [sub1483, sub1481]
  rfl
theorem sub1485 (p : Pattern) : d11 (change p 187 none) = d11 p := by
  change (if p 192 then d10 (change p 187 none) else d8 (change p 187 none)) = d11 p
  rw [sub1484, sub1481]
  rfl
theorem sub1486 (p : Pattern) : d125 (change p 187 none) = d11 p := by
  change d11 (change p 187 none) = d11 p
  exact sub1485 p
theorem sub1487 (p : Pattern) : d502 (change p 187 none) = d12 p := by
  change (if p 168 then d125 (change p 187 none) else d119 (change p 187 none)) = d12 p
  rw [sub1486, sub1474]
  rfl
theorem sub1488 (p : Pattern) : d5 (change p 187 none) = d5 p := by
  rfl
theorem sub1489 (p : Pattern) : d58 (change p 187 none) = d58 p := by
  change (if p 271 then d5 (change p 187 none) else d4 (change p 187 none)) = d58 p
  rw [sub1488, sub1475]
  rfl
theorem sub1490 (p : Pattern) : d59 (change p 187 none) = d59 p := by
  change (if p 193 then d58 (change p 187 none) else d9 (change p 187 none)) = d59 p
  rw [sub1489, sub1483]
  rfl
theorem sub1491 (p : Pattern) : d60 (change p 187 none) = d60 p := by
  change (if p 192 then d59 (change p 187 none) else d9 (change p 187 none)) = d60 p
  rw [sub1490, sub1483]
  rfl
theorem sub1492 (p : Pattern) : d143 (change p 187 none) = d61 p := by
  change (if p 186 then d60 (change p 187 none) else d125 (change p 187 none)) = d61 p
  rw [sub1491, sub1486]
  rfl
theorem sub1493 (p : Pattern) : d144 (change p 187 none) = d62 p := by
  change (if p 168 then d143 (change p 187 none) else d137 (change p 187 none)) = d62 p
  rw [sub1492, sub1478]
  rfl
theorem sub1494 (p : Pattern) : d503 (change p 187 none) = d63 p := by
  change (if p 160 then d144 (change p 187 none) else d502 (change p 187 none)) = d63 p
  rw [sub1493, sub1487]
  rfl
theorem sub1495 (p : Pattern) : d504 (change p 187 none) = d64 p := by
  change (if p 141 then d503 (change p 187 none) else d501 (change p 187 none)) = d64 p
  rw [sub1494, sub1479]
  rfl
theorem sub1496 (p : Pattern) : d505 (change p 187 none) = d106 p := by
  change (if p 160 then d55 (change p 187 none) else d119 (change p 187 none)) = d106 p
  rw [sub1477, sub1474]
  rfl
theorem sub1497 (p : Pattern) : d65 (change p 187 none) = d65 p := by
  change (if p 168 then d60 (change p 187 none) else d55 (change p 187 none)) = d65 p
  rw [sub1491, sub1477]
  rfl
theorem sub1498 (p : Pattern) : d506 (change p 187 none) = d109 p := by
  change (if p 160 then d65 (change p 187 none) else d502 (change p 187 none)) = d109 p
  rw [sub1497, sub1487]
  rfl
theorem sub1499 (p : Pattern) : d507 (change p 187 none) = d227 p := by
  change (if p 141 then d506 (change p 187 none) else d505 (change p 187 none)) = d227 p
  rw [sub1498, sub1496]
  rfl
theorem sub1500 (p : Pattern) : d508 (change p 187 none) = d228 p := by
  change (if p 134 then d507 (change p 187 none) else d504 (change p 187 none)) = d228 p
  rw [sub1499, sub1495]
  rfl
theorem sub1501 (p : Pattern) : d509 (change p 187 none) = d68 p := by
  change (if p 158 then d55 (change p 187 none) else d501 (change p 187 none)) = d68 p
  rw [sub1477, sub1479]
  rfl
theorem sub1502 (p : Pattern) : d510 (change p 187 none) = d69 p := by
  change (if p 158 then d65 (change p 187 none) else d503 (change p 187 none)) = d69 p
  rw [sub1497, sub1494]
  rfl
theorem sub1503 (p : Pattern) : d511 (change p 187 none) = d70 p := by
  change (if p 141 then d510 (change p 187 none) else d509 (change p 187 none)) = d70 p
  rw [sub1502, sub1501]
  rfl
theorem sub1504 (p : Pattern) : d512 (change p 187 none) = d229 p := by
  change (if p 158 then d55 (change p 187 none) else d505 (change p 187 none)) = d229 p
  rw [sub1477, sub1496]
  rfl
theorem sub1505 (p : Pattern) : d513 (change p 187 none) = d230 p := by
  change (if p 158 then d65 (change p 187 none) else d506 (change p 187 none)) = d230 p
  rw [sub1497, sub1498]
  rfl
theorem sub1506 (p : Pattern) : d514 (change p 187 none) = d231 p := by
  change (if p 141 then d513 (change p 187 none) else d512 (change p 187 none)) = d231 p
  rw [sub1505, sub1504]
  rfl
theorem sub1507 (p : Pattern) : d515 (change p 187 none) = d232 p := by
  change (if p 134 then d514 (change p 187 none) else d511 (change p 187 none)) = d232 p
  rw [sub1506, sub1503]
  rfl
theorem sub1508 (p : Pattern) : d516 (change p 187 none) = d233 p := by
  change (if p 133 then d515 (change p 187 none) else d508 (change p 187 none)) = d233 p
  rw [sub1507, sub1500]
  rfl
theorem sub1509 (p : Pattern) : d66 (change p 187 none) = d66 p := by
  change (if p 141 then d65 (change p 187 none) else d55 (change p 187 none)) = d66 p
  rw [sub1497, sub1477]
  rfl
theorem sub1510 (p : Pattern) : d517 (change p 187 none) = d234 p := by
  change (if p 133 then d66 (change p 187 none) else d515 (change p 187 none)) = d234 p
  rw [sub1509, sub1507]
  rfl
theorem sub1511 (p : Pattern) : d518 (change p 187 none) = d235 p := by
  change (if p 132 then d517 (change p 187 none) else d516 (change p 187 none)) = d235 p
  rw [sub1510, sub1508]
  rfl
theorem sub1512 (p : Pattern) : d519 (change p 187 none) = d67 p := by
  change (if p 134 then d66 (change p 187 none) else d504 (change p 187 none)) = d67 p
  rw [sub1509, sub1495]
  rfl
theorem sub1513 (p : Pattern) : d520 (change p 187 none) = d71 p := by
  change (if p 134 then d66 (change p 187 none) else d511 (change p 187 none)) = d71 p
  rw [sub1509, sub1503]
  rfl
theorem sub1514 (p : Pattern) : d521 (change p 187 none) = d72 p := by
  change (if p 133 then d520 (change p 187 none) else d519 (change p 187 none)) = d72 p
  rw [sub1513, sub1512]
  rfl
theorem sub1515 (p : Pattern) : d522 (change p 187 none) = d73 p := by
  change (if p 133 then d66 (change p 187 none) else d520 (change p 187 none)) = d73 p
  rw [sub1509, sub1513]
  rfl
theorem sub1516 (p : Pattern) : d523 (change p 187 none) = d74 p := by
  change (if p 132 then d522 (change p 187 none) else d521 (change p 187 none)) = d74 p
  rw [sub1515, sub1514]
  rfl
theorem sub1517 (p : Pattern) : d524 (change p 187 none) = d236 p := by
  change (if p 108 then d523 (change p 187 none) else d518 (change p 187 none)) = d236 p
  rw [sub1516, sub1511]
  rfl
theorem sub1518 (p : Pattern) : d0 (change p 160 (some 159)) = d0 p := by
  rfl
theorem sub1519 (p : Pattern) : d2 (change p 160 (some 159)) = d2 p := by
  rfl
theorem sub1520 (p : Pattern) : d6 (change p 160 (some 159)) = d6 p := by
  change (if p 193 then d2 (change p 160 (some 159)) else d0 (change p 160 (some 159))) = d6 p
  rw [sub1519, sub1518]
  rfl
theorem sub1521 (p : Pattern) : d7 (change p 160 (some 159)) = d7 p := by
  change (if p 192 then d6 (change p 160 (some 159)) else d0 (change p 160 (some 159))) = d7 p
  rw [sub1520, sub1518]
  rfl
theorem sub1522 (p : Pattern) : d106 (change p 160 (some 159)) = d7 p := by
  change d7 (change p 160 (some 159)) = d7 p
  exact sub1521 p
theorem sub1523 (p : Pattern) : d1 (change p 160 (some 159)) = d1 p := by
  rfl
theorem sub1524 (p : Pattern) : d8 (change p 160 (some 159)) = d8 p := by
  change (if p 271 then d1 (change p 160 (some 159)) else d0 (change p 160 (some 159))) = d8 p
  rw [sub1523, sub1518]
  rfl
theorem sub1525 (p : Pattern) : d3 (change p 160 (some 159)) = d3 p := by
  rfl
theorem sub1526 (p : Pattern) : d9 (change p 160 (some 159)) = d9 p := by
  change (if p 271 then d3 (change p 160 (some 159)) else d2 (change p 160 (some 159))) = d9 p
  rw [sub1525, sub1519]
  rfl
theorem sub1527 (p : Pattern) : d10 (change p 160 (some 159)) = d10 p := by
  change (if p 193 then d9 (change p 160 (some 159)) else d8 (change p 160 (some 159))) = d10 p
  rw [sub1526, sub1524]
  rfl
theorem sub1528 (p : Pattern) : d11 (change p 160 (some 159)) = d11 p := by
  change (if p 192 then d10 (change p 160 (some 159)) else d8 (change p 160 (some 159))) = d11 p
  rw [sub1527, sub1524]
  rfl
theorem sub1529 (p : Pattern) : d12 (change p 160 (some 159)) = d12 p := by
  change (if p 168 then d11 (change p 160 (some 159)) else d7 (change p 160 (some 159))) = d12 p
  rw [sub1528, sub1521]
  rfl
theorem sub1530 (p : Pattern) : d109 (change p 160 (some 159)) = d12 p := by
  change d12 (change p 160 (some 159)) = d12 p
  exact sub1529 p
theorem sub1531 (p : Pattern) : d227 (change p 160 (some 159)) = d13 p := by
  change (if p 141 then d109 (change p 160 (some 159)) else d106 (change p 160 (some 159))) = d13 p
  rw [sub1530, sub1522]
  rfl
theorem sub1532 (p : Pattern) : d4 (change p 160 (some 159)) = d4 p := by
  rfl
theorem sub1533 (p : Pattern) : d54 (change p 160 (some 159)) = d54 p := by
  change (if p 193 then d4 (change p 160 (some 159)) else d2 (change p 160 (some 159))) = d54 p
  rw [sub1532, sub1519]
  rfl
theorem sub1534 (p : Pattern) : d55 (change p 160 (some 159)) = d55 p := by
  change (if p 192 then d54 (change p 160 (some 159)) else d2 (change p 160 (some 159))) = d55 p
  rw [sub1533, sub1519]
  rfl
theorem sub1535 (p : Pattern) : d229 (change p 160 (some 159)) = d832 p := by
  change (if p 158 then d55 (change p 160 (some 159)) else d106 (change p 160 (some 159))) = d832 p
  rw [sub1534, sub1522]
  rfl
theorem sub1536 (p : Pattern) : d5 (change p 160 (some 159)) = d5 p := by
  rfl
theorem sub1537 (p : Pattern) : d58 (change p 160 (some 159)) = d58 p := by
  change (if p 271 then d5 (change p 160 (some 159)) else d4 (change p 160 (some 159))) = d58 p
  rw [sub1536, sub1532]
  rfl
theorem sub1538 (p : Pattern) : d59 (change p 160 (some 159)) = d59 p := by
  change (if p 193 then d58 (change p 160 (some 159)) else d9 (change p 160 (some 159))) = d59 p
  rw [sub1537, sub1526]
  rfl
theorem sub1539 (p : Pattern) : d60 (change p 160 (some 159)) = d60 p := by
  change (if p 192 then d59 (change p 160 (some 159)) else d9 (change p 160 (some 159))) = d60 p
  rw [sub1538, sub1526]
  rfl
theorem sub1540 (p : Pattern) : d65 (change p 160 (some 159)) = d65 p := by
  change (if p 168 then d60 (change p 160 (some 159)) else d55 (change p 160 (some 159))) = d65 p
  rw [sub1539, sub1534]
  rfl
theorem sub1541 (p : Pattern) : d230 (change p 160 (some 159)) = d833 p := by
  change (if p 158 then d65 (change p 160 (some 159)) else d109 (change p 160 (some 159))) = d833 p
  rw [sub1540, sub1530]
  rfl
theorem sub1542 (p : Pattern) : d231 (change p 160 (some 159)) = d834 p := by
  change (if p 141 then d230 (change p 160 (some 159)) else d229 (change p 160 (some 159))) = d834 p
  rw [sub1541, sub1535]
  rfl
theorem sub1543 (p : Pattern) : d366 (change p 160 (some 159)) = d835 p := by
  change (if p 133 then d231 (change p 160 (some 159)) else d227 (change p 160 (some 159))) = d835 p
  rw [sub1542, sub1531]
  rfl
theorem sub1544 (p : Pattern) : d66 (change p 160 (some 159)) = d66 p := by
  change (if p 141 then d65 (change p 160 (some 159)) else d55 (change p 160 (some 159))) = d66 p
  rw [sub1540, sub1534]
  rfl
theorem sub1545 (p : Pattern) : d367 (change p 160 (some 159)) = d836 p := by
  change (if p 133 then d66 (change p 160 (some 159)) else d231 (change p 160 (some 159))) = d836 p
  rw [sub1544, sub1542]
  rfl
theorem sub1546 (p : Pattern) : d368 (change p 160 (some 159)) = d837 p := by
  change (if p 132 then d367 (change p 160 (some 159)) else d366 (change p 160 (some 159))) = d837 p
  rw [sub1545, sub1543]
  rfl
theorem sub1547 (p : Pattern) : d369 (change p 160 (some 159)) = d838 p := by
  change (if p 134 then d66 (change p 160 (some 159)) else d227 (change p 160 (some 159))) = d838 p
  rw [sub1544, sub1531]
  rfl
theorem sub1548 (p : Pattern) : d370 (change p 160 (some 159)) = d839 p := by
  change (if p 134 then d66 (change p 160 (some 159)) else d231 (change p 160 (some 159))) = d839 p
  rw [sub1544, sub1542]
  rfl
theorem sub1549 (p : Pattern) : d371 (change p 160 (some 159)) = d840 p := by
  change (if p 133 then d370 (change p 160 (some 159)) else d369 (change p 160 (some 159))) = d840 p
  rw [sub1548, sub1547]
  rfl
theorem sub1550 (p : Pattern) : d372 (change p 160 (some 159)) = d841 p := by
  change (if p 133 then d66 (change p 160 (some 159)) else d370 (change p 160 (some 159))) = d841 p
  rw [sub1544, sub1548]
  rfl
theorem sub1551 (p : Pattern) : d373 (change p 160 (some 159)) = d842 p := by
  change (if p 132 then d372 (change p 160 (some 159)) else d371 (change p 160 (some 159))) = d842 p
  rw [sub1550, sub1549]
  rfl
theorem sub1552 (p : Pattern) : d374 (change p 160 (some 159)) = d843 p := by
  change (if p 108 then d373 (change p 160 (some 159)) else d368 (change p 160 (some 159))) = d843 p
  rw [sub1551, sub1546]
  rfl
theorem sub1553 (p : Pattern) : d0 (change p 192 none) = d0 p := by
  rfl
theorem sub1554 (p : Pattern) : d24 (change p 192 none) = d0 p := by
  change d0 (change p 192 none) = d0 p
  exact sub1553 p
theorem sub1555 (p : Pattern) : d2 (change p 192 none) = d2 p := by
  rfl
theorem sub1556 (p : Pattern) : d525 (change p 192 none) = d2 p := by
  change d2 (change p 192 none) = d2 p
  exact sub1555 p
theorem sub1557 (p : Pattern) : d526 (change p 192 none) = d45 p := by
  change (if p 186 then d525 (change p 192 none) else d24 (change p 192 none)) = d45 p
  rw [sub1556, sub1554]
  rfl
theorem sub1558 (p : Pattern) : d527 (change p 192 none) = d46 p := by
  change (if p 160 then d526 (change p 192 none) else d24 (change p 192 none)) = d46 p
  rw [sub1557, sub1554]
  rfl
theorem sub1559 (p : Pattern) : d1 (change p 192 none) = d1 p := by
  rfl
end NetHack.Sokoban12CostPartition
