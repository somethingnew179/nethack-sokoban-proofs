/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions09
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1500 (pattern : Twelve) : d818 (change pattern 4 5) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d814 (change pattern 4 5)) = d818 pattern
  rw [s1421, s1494]
  rfl
theorem s1501 (pattern : Twelve) : d826 (change pattern 4 5) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 4 5) else d34 (change pattern 4 5)) = d826 pattern
  rw [s1500, s1499]
  rfl
theorem s1502 (pattern : Twelve) : d840 (change pattern 4 5) = d826 pattern := by
  change d826 (change pattern 4 5) = d826 pattern
  exact s1501 pattern
theorem s1503 (pattern : Twelve) : d981 (change pattern 4 5) = d826 pattern := by
  change d840 (change pattern 4 5) = d826 pattern
  exact s1502 pattern
theorem s1504 (pattern : Twelve) : d991 (change pattern 4 5) = d2036 pattern := by
  change (if pattern.j then d981 (change pattern 4 5) else d980 (change pattern 4 5)) = d2036 pattern
  rw [s1503, s1498]
  rfl
theorem s1505 (pattern : Twelve) : d982 (change pattern 4 5) = d824 pattern := by
  change d838 (change pattern 4 5) = d824 pattern
  exact s1497 pattern
theorem s1506 (pattern : Twelve) : d983 (change pattern 4 5) = d826 pattern := by
  change d840 (change pattern 4 5) = d826 pattern
  exact s1502 pattern
theorem s1507 (pattern : Twelve) : d992 (change pattern 4 5) = d2036 pattern := by
  change (if pattern.j then d983 (change pattern 4 5) else d982 (change pattern 4 5)) = d2036 pattern
  rw [s1506, s1505]
  rfl
theorem s1508 (pattern : Twelve) : d1000 (change pattern 4 5) = d2036 pattern := by
  change (if pattern.d then d992 (change pattern 4 5) else d991 (change pattern 4 5)) = d2036 pattern
  rw [s1507, s1504]
  simp only [ite_self]
theorem s1509 (pattern : Twelve) : d819 (change pattern 4 5) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 4 5) else d814 (change pattern 4 5)) = d819 pattern
  rw [s1438, s1494]
  rfl
theorem s1510 (pattern : Twelve) : d828 (change pattern 4 5) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 4 5) else d34 (change pattern 4 5)) = d828 pattern
  rw [s1509, s1499]
  rfl
theorem s1511 (pattern : Twelve) : d842 (change pattern 4 5) = d828 pattern := by
  change d828 (change pattern 4 5) = d828 pattern
  exact s1510 pattern
theorem s1512 (pattern : Twelve) : d984 (change pattern 4 5) = d828 pattern := by
  change d842 (change pattern 4 5) = d828 pattern
  exact s1511 pattern
theorem s1513 (pattern : Twelve) : d15 (change pattern 4 5) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 4 5) else d4 (change pattern 4 5)) = d15 pattern
  rw [s1423, s1420]
  rfl
theorem s1514 (pattern : Twelve) : d24 (change pattern 4 5) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 4 5) else d4 (change pattern 4 5)) = d24 pattern
  rw [s1513, s1420]
  rfl
theorem s1515 (pattern : Twelve) : d41 (change pattern 4 5) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 4 5) else d23 (change pattern 4 5)) = d41 pattern
  rw [s1514, s1445]
  rfl
theorem s1516 (pattern : Twelve) : d815 (change pattern 4 5) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 4 5) else d9 (change pattern 4 5)) = d815 pattern
  rw [s1438, s1444]
  rfl
theorem s1517 (pattern : Twelve) : d820 (change pattern 4 5) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d815 (change pattern 4 5)) = d820 pattern
  rw [s1421, s1516]
  rfl
theorem s1518 (pattern : Twelve) : d829 (change pattern 4 5) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 4 5) else d41 (change pattern 4 5)) = d829 pattern
  rw [s1517, s1515]
  rfl
theorem s1519 (pattern : Twelve) : d844 (change pattern 4 5) = d829 pattern := by
  change d829 (change pattern 4 5) = d829 pattern
  exact s1518 pattern
theorem s1520 (pattern : Twelve) : d985 (change pattern 4 5) = d829 pattern := by
  change d844 (change pattern 4 5) = d829 pattern
  exact s1519 pattern
theorem s1521 (pattern : Twelve) : d993 (change pattern 4 5) = d2037 pattern := by
  change (if pattern.j then d985 (change pattern 4 5) else d984 (change pattern 4 5)) = d2037 pattern
  rw [s1520, s1512]
  rfl
theorem s1522 (pattern : Twelve) : d994 (change pattern 4 5) = d2038 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d983 (change pattern 4 5)) = d2038 pattern
  rw [s1421, s1506]
  rfl
theorem s1523 (pattern : Twelve) : d1001 (change pattern 4 5) = d2039 pattern := by
  change (if pattern.d then d994 (change pattern 4 5) else d993 (change pattern 4 5)) = d2039 pattern
  rw [s1522, s1521]
  rfl
theorem s1524 (pattern : Twelve) : d1004 (change pattern 4 5) = d2040 pattern := by
  change (if pattern.c then d1001 (change pattern 4 5) else d1000 (change pattern 4 5)) = d2040 pattern
  rw [s1523, s1508]
  rfl
theorem s1525 (pattern : Twelve) : d986 (change pattern 4 5) = d824 pattern := by
  change d838 (change pattern 4 5) = d824 pattern
  exact s1497 pattern
theorem s1526 (pattern : Twelve) : d832 (change pattern 4 5) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 4 5) else d34 (change pattern 4 5)) = d832 pattern
  rw [s1461, s1499]
  rfl
theorem s1527 (pattern : Twelve) : d847 (change pattern 4 5) = d832 pattern := by
  change d832 (change pattern 4 5) = d832 pattern
  exact s1526 pattern
theorem s1528 (pattern : Twelve) : d987 (change pattern 4 5) = d832 pattern := by
  change d847 (change pattern 4 5) = d832 pattern
  exact s1527 pattern
theorem s1529 (pattern : Twelve) : d995 (change pattern 4 5) = d2041 pattern := by
  change (if pattern.j then d987 (change pattern 4 5) else d986 (change pattern 4 5)) = d2041 pattern
  rw [s1528, s1525]
  rfl
theorem s1530 (pattern : Twelve) : d834 (change pattern 4 5) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 4 5) else d34 (change pattern 4 5)) = d834 pattern
  rw [s1467, s1499]
  rfl
theorem s1531 (pattern : Twelve) : d849 (change pattern 4 5) = d834 pattern := by
  change d834 (change pattern 4 5) = d834 pattern
  exact s1530 pattern
theorem s1532 (pattern : Twelve) : d988 (change pattern 4 5) = d834 pattern := by
  change d849 (change pattern 4 5) = d834 pattern
  exact s1531 pattern
theorem s1533 (pattern : Twelve) : d836 (change pattern 4 5) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 4 5) else d41 (change pattern 4 5)) = d836 pattern
  rw [s1471, s1515]
  rfl
theorem s1534 (pattern : Twelve) : d851 (change pattern 4 5) = d836 pattern := by
  change d836 (change pattern 4 5) = d836 pattern
  exact s1533 pattern
theorem s1535 (pattern : Twelve) : d989 (change pattern 4 5) = d836 pattern := by
  change d851 (change pattern 4 5) = d836 pattern
  exact s1534 pattern
theorem s1536 (pattern : Twelve) : d996 (change pattern 4 5) = d2042 pattern := by
  change (if pattern.j then d989 (change pattern 4 5) else d988 (change pattern 4 5)) = d2042 pattern
  rw [s1535, s1532]
  rfl
theorem s1537 (pattern : Twelve) : d997 (change pattern 4 5) = d2043 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d987 (change pattern 4 5)) = d2043 pattern
  rw [s1421, s1528]
  rfl
theorem s1538 (pattern : Twelve) : d1002 (change pattern 4 5) = d2044 pattern := by
  change (if pattern.d then d997 (change pattern 4 5) else d996 (change pattern 4 5)) = d2044 pattern
  rw [s1537, s1536]
  rfl
theorem s1539 (pattern : Twelve) : d1005 (change pattern 4 5) = d2045 pattern := by
  change (if pattern.c then d1002 (change pattern 4 5) else d995 (change pattern 4 5)) = d2045 pattern
  rw [s1538, s1529]
  rfl
theorem s1540 (pattern : Twelve) : d1007 (change pattern 4 5) = d2046 pattern := by
  change (if pattern.g then d1005 (change pattern 4 5) else d1004 (change pattern 4 5)) = d2046 pattern
  rw [s1539, s1524]
  rfl
theorem s1541 (pattern : Twelve) : d998 (change pattern 4 5) = d2036 pattern := by
  change (if pattern.j then d983 (change pattern 4 5) else d986 (change pattern 4 5)) = d2036 pattern
  rw [s1506, s1525]
  rfl
theorem s1542 (pattern : Twelve) : d990 (change pattern 4 5) = d828 pattern := by
  change d842 (change pattern 4 5) = d828 pattern
  exact s1511 pattern
theorem s1543 (pattern : Twelve) : d999 (change pattern 4 5) = d2037 pattern := by
  change (if pattern.j then d985 (change pattern 4 5) else d990 (change pattern 4 5)) = d2037 pattern
  rw [s1520, s1542]
  rfl
theorem s1544 (pattern : Twelve) : d1003 (change pattern 4 5) = d2039 pattern := by
  change (if pattern.d then d994 (change pattern 4 5) else d999 (change pattern 4 5)) = d2039 pattern
  rw [s1522, s1543]
  rfl
theorem s1545 (pattern : Twelve) : d1006 (change pattern 4 5) = d2040 pattern := by
  change (if pattern.c then d1003 (change pattern 4 5) else d998 (change pattern 4 5)) = d2040 pattern
  rw [s1544, s1541]
  rfl
theorem s1546 (pattern : Twelve) : d1008 (change pattern 4 5) = d2046 pattern := by
  change (if pattern.g then d1005 (change pattern 4 5) else d1006 (change pattern 4 5)) = d2046 pattern
  rw [s1539, s1545]
  rfl
theorem s1547 (pattern : Twelve) : d1009 (change pattern 4 5) = d2046 pattern := by
  change (if pattern.b then d1008 (change pattern 4 5) else d1007 (change pattern 4 5)) = d2046 pattern
  rw [s1546, s1540]
  simp only [ite_self]
theorem s1548 (pattern : Twelve) : d1010 (change pattern 4 5) = d2046 pattern := by
  change (if pattern.a then d1008 (change pattern 4 5) else d1009 (change pattern 4 5)) = d2046 pattern
  rw [s1546, s1547]
  simp only [ite_self]
theorem s1549 (pattern : Twelve) : d8 (change pattern 4 5) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 4 5) else d1 (change pattern 4 5)) = d8 pattern
  rw [s1418, s1410]
  rfl
theorem s1550 (pattern : Twelve) : d1275 (change pattern 4 5) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 4 5) else d7 (change pattern 4 5)) = d1275 pattern
  rw [s1549, s1412]
  rfl
theorem s1551 (pattern : Twelve) : d872 (change pattern 4 5) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 4 5) else d1 (change pattern 4 5)) = d872 pattern
  rw [s1549, s1410]
  rfl
theorem s1552 (pattern : Twelve) : d1278 (change pattern 4 5) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 4 5) else d1275 (change pattern 4 5)) = d1278 pattern
  rw [s1551, s1550]
  rfl
theorem s1553 (pattern : Twelve) : d1284 (change pattern 4 5) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 4 5) else d1278 (change pattern 4 5)) = d1284 pattern
  rw [s1551, s1552]
  rfl
theorem s1554 (pattern : Twelve) : d1293 (change pattern 4 5) = d1284 pattern := by
  change d1284 (change pattern 4 5) = d1284 pattern
  exact s1553 pattern
theorem s1555 (pattern : Twelve) : d1412 (change pattern 4 5) = d1284 pattern := by
  change d1293 (change pattern 4 5) = d1284 pattern
  exact s1554 pattern
theorem s1556 (pattern : Twelve) : d117 (change pattern 4 5) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 4 5) else d3 (change pattern 4 5)) = d117 pattern
  rw [s1420, s1438]
  rfl
theorem s1557 (pattern : Twelve) : d1276 (change pattern 4 5) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 4 5) else d9 (change pattern 4 5)) = d1276 pattern
  rw [s1556, s1444]
  rfl
theorem s1558 (pattern : Twelve) : d1279 (change pattern 4 5) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 4 5) else d1275 (change pattern 4 5)) = d1279 pattern
  rw [s1557, s1550]
  rfl
theorem s1559 (pattern : Twelve) : d1280 (change pattern 4 5) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d872 (change pattern 4 5)) = d1280 pattern
  rw [s1421, s1551]
  rfl
theorem s1560 (pattern : Twelve) : d1285 (change pattern 4 5) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 4 5) else d1279 (change pattern 4 5)) = d1285 pattern
  rw [s1559, s1558]
  rfl
theorem s1561 (pattern : Twelve) : d1295 (change pattern 4 5) = d1285 pattern := by
  change d1285 (change pattern 4 5) = d1285 pattern
  exact s1560 pattern
theorem s1562 (pattern : Twelve) : d1413 (change pattern 4 5) = d1285 pattern := by
  change d1295 (change pattern 4 5) = d1285 pattern
  exact s1561 pattern
theorem s1563 (pattern : Twelve) : d1417 (change pattern 4 5) = d2047 pattern := by
  change (if pattern.j then d1413 (change pattern 4 5) else d1412 (change pattern 4 5)) = d2047 pattern
  rw [s1562, s1555]
  rfl
theorem s1564 (pattern : Twelve) : d1414 (change pattern 4 5) = d1284 pattern := by
  change d1293 (change pattern 4 5) = d1284 pattern
  exact s1554 pattern
theorem s1565 (pattern : Twelve) : d1418 (change pattern 4 5) = d2047 pattern := by
  change (if pattern.j then d1413 (change pattern 4 5) else d1414 (change pattern 4 5)) = d2047 pattern
  rw [s1562, s1564]
  rfl
theorem s1566 (pattern : Twelve) : d1421 (change pattern 4 5) = d2047 pattern := by
  change (if pattern.d then d1418 (change pattern 4 5) else d1417 (change pattern 4 5)) = d2047 pattern
  rw [s1565, s1563]
  simp only [ite_self]
theorem s1567 (pattern : Twelve) : d119 (change pattern 4 5) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 4 5) else d3 (change pattern 4 5)) = d119 pattern
  rw [s1556, s1438]
  rfl
theorem s1568 (pattern : Twelve) : d1281 (change pattern 4 5) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 4 5) else d872 (change pattern 4 5)) = d1281 pattern
  rw [s1567, s1551]
  rfl
theorem s1569 (pattern : Twelve) : d1287 (change pattern 4 5) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 4 5) else d1279 (change pattern 4 5)) = d1287 pattern
  rw [s1568, s1558]
  rfl
theorem s1570 (pattern : Twelve) : d1297 (change pattern 4 5) = d1287 pattern := by
  change d1287 (change pattern 4 5) = d1287 pattern
  exact s1569 pattern
theorem s1571 (pattern : Twelve) : d1415 (change pattern 4 5) = d1287 pattern := by
  change d1297 (change pattern 4 5) = d1287 pattern
  exact s1570 pattern
theorem s1572 (pattern : Twelve) : d1277 (change pattern 4 5) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 4 5) else d15 (change pattern 4 5)) = d1277 pattern
  rw [s1424, s1513]
  rfl
theorem s1573 (pattern : Twelve) : d1282 (change pattern 4 5) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 4 5) else d1276 (change pattern 4 5)) = d1282 pattern
  rw [s1572, s1557]
  rfl
theorem s1574 (pattern : Twelve) : d125 (change pattern 4 5) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d119 (change pattern 4 5)) = d125 pattern
  rw [s1421, s1567]
  rfl
theorem s1575 (pattern : Twelve) : d1288 (change pattern 4 5) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 4 5) else d1282 (change pattern 4 5)) = d1288 pattern
  rw [s1574, s1573]
  rfl
theorem s1576 (pattern : Twelve) : d1299 (change pattern 4 5) = d1288 pattern := by
  change d1288 (change pattern 4 5) = d1288 pattern
  exact s1575 pattern
theorem s1577 (pattern : Twelve) : d1416 (change pattern 4 5) = d1288 pattern := by
  change d1299 (change pattern 4 5) = d1288 pattern
  exact s1576 pattern
theorem s1578 (pattern : Twelve) : d1419 (change pattern 4 5) = d2048 pattern := by
  change (if pattern.j then d1416 (change pattern 4 5) else d1415 (change pattern 4 5)) = d2048 pattern
  rw [s1577, s1571]
  rfl
theorem s1579 (pattern : Twelve) : d1420 (change pattern 4 5) = d2049 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d1413 (change pattern 4 5)) = d2049 pattern
  rw [s1421, s1562]
  rfl
theorem s1580 (pattern : Twelve) : d1422 (change pattern 4 5) = d2050 pattern := by
  change (if pattern.d then d1420 (change pattern 4 5) else d1419 (change pattern 4 5)) = d2050 pattern
  rw [s1579, s1578]
  rfl
theorem s1581 (pattern : Twelve) : d1423 (change pattern 4 5) = d2051 pattern := by
  change (if pattern.c then d1422 (change pattern 4 5) else d1421 (change pattern 4 5)) = d2051 pattern
  rw [s1580, s1566]
  rfl
theorem s1582 (pattern : Twelve) : d1424 (change pattern 4 5) = d2051 pattern := by
  change (if pattern.c then d1422 (change pattern 4 5) else d1418 (change pattern 4 5)) = d2051 pattern
  rw [s1580, s1565]
  rfl
theorem s1583 (pattern : Twelve) : d1425 (change pattern 4 5) = d2051 pattern := by
  change (if pattern.g then d1424 (change pattern 4 5) else d1423 (change pattern 4 5)) = d2051 pattern
  rw [s1582, s1581]
  simp only [ite_self]
theorem s1584 (pattern : Twelve) : d1426 (change pattern 4 5) = d2051 pattern := by
  change (if pattern.b then d1424 (change pattern 4 5) else d1425 (change pattern 4 5)) = d2051 pattern
  rw [s1582, s1583]
  simp only [ite_self]
theorem s1585 (pattern : Twelve) : d1427 (change pattern 4 5) = d2051 pattern := by
  change (if pattern.a then d1424 (change pattern 4 5) else d1426 (change pattern 4 5)) = d2051 pattern
  rw [s1582, s1584]
  simp only [ite_self]
theorem s1586 (pattern : Twelve) : d11 (change pattern 4 5) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 4 5) else d1 (change pattern 4 5)) = d11 pattern
  rw [s1438, s1410]
  rfl
theorem s1587 (pattern : Twelve) : d16 (change pattern 4 5) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 4 5) else d2 (change pattern 4 5)) = d16 pattern
  rw [s1420, s1418]
  rfl
theorem s1588 (pattern : Twelve) : d1324 (change pattern 4 5) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 4 5) else d11 (change pattern 4 5)) = d1324 pattern
  rw [s1587, s1586]
  rfl
theorem s1589 (pattern : Twelve) : d1649 (change pattern 4 5) = d1324 pattern := by
  change d1324 (change pattern 4 5) = d1324 pattern
  exact s1588 pattern
theorem s1590 (pattern : Twelve) : d1705 (change pattern 4 5) = d1324 pattern := by
  change d1649 (change pattern 4 5) = d1324 pattern
  exact s1589 pattern
theorem s1591 (pattern : Twelve) : d12 (change pattern 4 5) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 4 5) else d3 (change pattern 4 5)) = d12 pattern
  rw [s1423, s1438]
  rfl
theorem s1592 (pattern : Twelve) : d20 (change pattern 4 5) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 4 5) else d12 (change pattern 4 5)) = d20 pattern
  rw [s1422, s1591]
  rfl
theorem s1593 (pattern : Twelve) : d1644 (change pattern 4 5) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 4 5) else d1324 (change pattern 4 5)) = d1644 pattern
  rw [s1592, s1588]
  rfl
theorem s1594 (pattern : Twelve) : d1645 (change pattern 4 5) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d1324 (change pattern 4 5)) = d1645 pattern
  rw [s1421, s1588]
  rfl
theorem s1595 (pattern : Twelve) : d1647 (change pattern 4 5) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 4 5) else d1644 (change pattern 4 5)) = d1647 pattern
  rw [s1594, s1593]
  rfl
theorem s1596 (pattern : Twelve) : d1651 (change pattern 4 5) = d1647 pattern := by
  change d1647 (change pattern 4 5) = d1647 pattern
  exact s1595 pattern
theorem s1597 (pattern : Twelve) : d1706 (change pattern 4 5) = d1647 pattern := by
  change d1651 (change pattern 4 5) = d1647 pattern
  exact s1596 pattern
theorem s1598 (pattern : Twelve) : d1709 (change pattern 4 5) = d2052 pattern := by
  change (if pattern.j then d1706 (change pattern 4 5) else d1705 (change pattern 4 5)) = d2052 pattern
  rw [s1597, s1590]
  rfl
theorem s1599 (pattern : Twelve) : d1652 (change pattern 4 5) = d1644 pattern := by
  change d1644 (change pattern 4 5) = d1644 pattern
  exact s1593 pattern
theorem s1600 (pattern : Twelve) : d1707 (change pattern 4 5) = d1644 pattern := by
  change d1652 (change pattern 4 5) = d1644 pattern
  exact s1599 pattern
theorem s1601 (pattern : Twelve) : d22 (change pattern 4 5) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 4 5) else d14 (change pattern 4 5)) = d22 pattern
  rw [s1421, s1424]
  rfl
theorem s1602 (pattern : Twelve) : d1646 (change pattern 4 5) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 4 5) else d20 (change pattern 4 5)) = d1646 pattern
  rw [s1601, s1592]
  rfl
theorem s1603 (pattern : Twelve) : d128 (change pattern 4 5) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 4 5) else d20 (change pattern 4 5)) = d128 pattern
  rw [s1421, s1592]
  rfl
theorem s1604 (pattern : Twelve) : d1648 (change pattern 4 5) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 4 5) else d1646 (change pattern 4 5)) = d1648 pattern
  rw [s1603, s1602]
  rfl
theorem s1605 (pattern : Twelve) : d1654 (change pattern 4 5) = d1648 pattern := by
  change d1648 (change pattern 4 5) = d1648 pattern
  exact s1604 pattern
theorem s1606 (pattern : Twelve) : d1708 (change pattern 4 5) = d1648 pattern := by
  change d1654 (change pattern 4 5) = d1648 pattern
  exact s1605 pattern
theorem s1607 (pattern : Twelve) : d1710 (change pattern 4 5) = d2053 pattern := by
  change (if pattern.j then d1708 (change pattern 4 5) else d1707 (change pattern 4 5)) = d2053 pattern
  rw [s1606, s1600]
  rfl
theorem s1608 (pattern : Twelve) : d1711 (change pattern 4 5) = d2054 pattern := by
  change (if pattern.j then d6 (change pattern 4 5) else d1706 (change pattern 4 5)) = d2054 pattern
  rw [s1421, s1597]
  rfl
theorem s1609 (pattern : Twelve) : d1712 (change pattern 4 5) = d2055 pattern := by
  change (if pattern.d then d1711 (change pattern 4 5) else d1710 (change pattern 4 5)) = d2055 pattern
  rw [s1608, s1607]
  rfl
theorem s1610 (pattern : Twelve) : d1713 (change pattern 4 5) = d2056 pattern := by
  change (if pattern.c then d1712 (change pattern 4 5) else d1709 (change pattern 4 5)) = d2056 pattern
  rw [s1609, s1598]
  rfl
theorem s1611 (pattern : Twelve) : d0 (change pattern 12 10) = d0 pattern := by
  rfl
theorem s1612 (pattern : Twelve) : d1 (change pattern 12 10) = d1 pattern := by
  rfl
theorem s1613 (pattern : Twelve) : d26 (change pattern 12 10) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 10) else d0 (change pattern 12 10)) = d26 pattern
  rw [s1612, s1611]
  rfl
theorem s1614 (pattern : Twelve) : d7 (change pattern 12 10) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 10) else d0 (change pattern 12 10)) = d7 pattern
  rw [s1612, s1611]
  rfl
theorem s1615 (pattern : Twelve) : d17 (change pattern 12 10) = d7 pattern := by
  change d7 (change pattern 12 10) = d7 pattern
  exact s1614 pattern
theorem s1616 (pattern : Twelve) : d27 (change pattern 12 10) = d2057 pattern := by
  change (if pattern.i then d1 (change pattern 12 10) else d17 (change pattern 12 10)) = d2057 pattern
  rw [s1612, s1615]
  rfl
theorem s1617 (pattern : Twelve) : d50 (change pattern 12 10) = d2058 pattern := by
  change (if pattern.h then d27 (change pattern 12 10) else d26 (change pattern 12 10)) = d2058 pattern
  rw [s1616, s1613]
  rfl
theorem s1618 (pattern : Twelve) : d72 (change pattern 12 10) = d2059 pattern := by
  change (if pattern.f then d50 (change pattern 12 10) else d0 (change pattern 12 10)) = d2059 pattern
  rw [s1617, s1611]
  rfl
theorem s1619 (pattern : Twelve) : d2 (change pattern 12 10) = d2 pattern := by
  rfl
theorem s1620 (pattern : Twelve) : d3 (change pattern 12 10) = d3 pattern := by
  rfl
theorem s1621 (pattern : Twelve) : d9 (change pattern 12 10) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 10) else d2 (change pattern 12 10)) = d9 pattern
  rw [s1620, s1619]
  rfl
theorem s1622 (pattern : Twelve) : d18 (change pattern 12 10) = d9 pattern := by
  change d9 (change pattern 12 10) = d9 pattern
  exact s1621 pattern
theorem s1623 (pattern : Twelve) : d28 (change pattern 12 10) = d2060 pattern := by
  change (if pattern.i then d18 (change pattern 12 10) else d17 (change pattern 12 10)) = d2060 pattern
  rw [s1622, s1615]
  rfl
theorem s1624 (pattern : Twelve) : d11 (change pattern 12 10) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 10) else d1 (change pattern 12 10)) = d11 pattern
  rw [s1620, s1612]
  rfl
theorem s1625 (pattern : Twelve) : d19 (change pattern 12 10) = d11 pattern := by
  change d11 (change pattern 12 10) = d11 pattern
  exact s1624 pattern
theorem s1626 (pattern : Twelve) : d6 (change pattern 12 10) = d6 pattern := by
  rfl
theorem s1627 (pattern : Twelve) : d29 (change pattern 12 10) = d2061 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d19 (change pattern 12 10)) = d2061 pattern
  rw [s1626, s1625]
  rfl
theorem s1628 (pattern : Twelve) : d51 (change pattern 12 10) = d2062 pattern := by
  change (if pattern.h then d29 (change pattern 12 10) else d28 (change pattern 12 10)) = d2062 pattern
  rw [s1627, s1623]
  rfl
theorem s1629 (pattern : Twelve) : d73 (change pattern 12 10) = d2063 pattern := by
  change (if pattern.f then d51 (change pattern 12 10) else d0 (change pattern 12 10)) = d2063 pattern
  rw [s1628, s1611]
  rfl
theorem s1630 (pattern : Twelve) : d91 (change pattern 12 10) = d2064 pattern := by
  change (if pattern.e then d73 (change pattern 12 10) else d72 (change pattern 12 10)) = d2064 pattern
  rw [s1629, s1618]
  rfl
theorem s1631 (pattern : Twelve) : d30 (change pattern 12 10) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 10) else d0 (change pattern 12 10)) = d30 pattern
  rw [s1619, s1611]
  rfl
theorem s1632 (pattern : Twelve) : d4 (change pattern 12 10) = d4 pattern := by
  rfl
theorem s1633 (pattern : Twelve) : d13 (change pattern 12 10) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 10) else d4 (change pattern 12 10)) = d13 pattern
  rw [s1626, s1632]
  rfl
theorem s1634 (pattern : Twelve) : d20 (change pattern 12 10) = d13 pattern := by
  change d13 (change pattern 12 10) = d13 pattern
  exact s1633 pattern
theorem s1635 (pattern : Twelve) : d31 (change pattern 12 10) = d2065 pattern := by
  change (if pattern.i then d20 (change pattern 12 10) else d0 (change pattern 12 10)) = d2065 pattern
  rw [s1634, s1611]
  rfl
theorem s1636 (pattern : Twelve) : d52 (change pattern 12 10) = d2066 pattern := by
  change (if pattern.h then d31 (change pattern 12 10) else d30 (change pattern 12 10)) = d2066 pattern
  rw [s1635, s1631]
  rfl
theorem s1637 (pattern : Twelve) : d5 (change pattern 12 10) = d5 pattern := by
  rfl
theorem s1638 (pattern : Twelve) : d14 (change pattern 12 10) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 10) else d5 (change pattern 12 10)) = d14 pattern
  rw [s1626, s1637]
  rfl
theorem s1639 (pattern : Twelve) : d21 (change pattern 12 10) = d14 pattern := by
  change d14 (change pattern 12 10) = d14 pattern
  exact s1638 pattern
theorem s1640 (pattern : Twelve) : d32 (change pattern 12 10) = d2067 pattern := by
  change (if pattern.i then d21 (change pattern 12 10) else d17 (change pattern 12 10)) = d2067 pattern
  rw [s1639, s1615]
  rfl
theorem s1641 (pattern : Twelve) : d53 (change pattern 12 10) = d2068 pattern := by
  change (if pattern.h then d32 (change pattern 12 10) else d30 (change pattern 12 10)) = d2068 pattern
  rw [s1640, s1631]
  rfl
theorem s1642 (pattern : Twelve) : d74 (change pattern 12 10) = d2069 pattern := by
  change (if pattern.f then d53 (change pattern 12 10) else d52 (change pattern 12 10)) = d2069 pattern
  rw [s1641, s1636]
  rfl
theorem s1643 (pattern : Twelve) : d22 (change pattern 12 10) = d6 pattern := by
  change d6 (change pattern 12 10) = d6 pattern
  exact s1626 pattern
theorem s1644 (pattern : Twelve) : d33 (change pattern 12 10) = d35 pattern := by
  change (if pattern.i then d22 (change pattern 12 10) else d0 (change pattern 12 10)) = d35 pattern
  rw [s1643, s1611]
  rfl
theorem s1645 (pattern : Twelve) : d54 (change pattern 12 10) = d56 pattern := by
  change (if pattern.h then d33 (change pattern 12 10) else d30 (change pattern 12 10)) = d56 pattern
  rw [s1644, s1631]
  rfl
theorem s1646 (pattern : Twelve) : d23 (change pattern 12 10) = d9 pattern := by
  change d9 (change pattern 12 10) = d9 pattern
  exact s1621 pattern
theorem s1647 (pattern : Twelve) : d34 (change pattern 12 10) = d2060 pattern := by
  change (if pattern.i then d23 (change pattern 12 10) else d17 (change pattern 12 10)) = d2060 pattern
  rw [s1646, s1615]
  rfl
theorem s1648 (pattern : Twelve) : d55 (change pattern 12 10) = d2062 pattern := by
  change (if pattern.h then d29 (change pattern 12 10) else d34 (change pattern 12 10)) = d2062 pattern
  rw [s1627, s1647]
  rfl
theorem s1649 (pattern : Twelve) : d75 (change pattern 12 10) = d2070 pattern := by
  change (if pattern.f then d55 (change pattern 12 10) else d54 (change pattern 12 10)) = d2070 pattern
  rw [s1648, s1645]
  rfl
end NetHack.Sokoban21.Diagram
