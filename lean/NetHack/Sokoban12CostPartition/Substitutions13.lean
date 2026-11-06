/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1560 (p : Pattern) : d8 (change p 192 none) = d8 p := by
  change (if p 271 then d1 (change p 192 none) else d0 (change p 192 none)) = d8 p
  rw [sub1559, sub1553]
  rfl
theorem sub1561 (p : Pattern) : d25 (change p 192 none) = d8 p := by
  change d8 (change p 192 none) = d8 p
  exact sub1560 p
theorem sub1562 (p : Pattern) : d26 (change p 192 none) = d1055 p := by
  change (if p 168 then d25 (change p 192 none) else d24 (change p 192 none)) = d1055 p
  rw [sub1561, sub1554]
  rfl
theorem sub1563 (p : Pattern) : d3 (change p 192 none) = d3 p := by
  rfl
theorem sub1564 (p : Pattern) : d9 (change p 192 none) = d9 p := by
  change (if p 271 then d3 (change p 192 none) else d2 (change p 192 none)) = d9 p
  rw [sub1563, sub1555]
  rfl
theorem sub1565 (p : Pattern) : d528 (change p 192 none) = d9 p := by
  change d9 (change p 192 none) = d9 p
  exact sub1564 p
theorem sub1566 (p : Pattern) : d529 (change p 192 none) = d1056 p := by
  change (if p 186 then d528 (change p 192 none) else d25 (change p 192 none)) = d1056 p
  rw [sub1565, sub1561]
  rfl
theorem sub1567 (p : Pattern) : d530 (change p 192 none) = d1057 p := by
  change (if p 168 then d529 (change p 192 none) else d526 (change p 192 none)) = d1057 p
  rw [sub1566, sub1557]
  rfl
theorem sub1568 (p : Pattern) : d531 (change p 192 none) = d1058 p := by
  change (if p 160 then d530 (change p 192 none) else d26 (change p 192 none)) = d1058 p
  rw [sub1567, sub1562]
  rfl
theorem sub1569 (p : Pattern) : d532 (change p 192 none) = d1059 p := by
  change (if p 141 then d531 (change p 192 none) else d527 (change p 192 none)) = d1059 p
  rw [sub1568, sub1558]
  rfl
theorem sub1570 (p : Pattern) : d533 (change p 192 none) = d76 p := by
  change (if p 160 then d525 (change p 192 none) else d24 (change p 192 none)) = d76 p
  rw [sub1556, sub1554]
  rfl
theorem sub1571 (p : Pattern) : d534 (change p 192 none) = d82 p := by
  change (if p 187 then d525 (change p 192 none) else d24 (change p 192 none)) = d82 p
  rw [sub1556, sub1554]
  rfl
theorem sub1572 (p : Pattern) : d535 (change p 192 none) = d83 p := by
  change (if p 186 then d534 (change p 192 none) else d24 (change p 192 none)) = d83 p
  rw [sub1571, sub1554]
  rfl
theorem sub1573 (p : Pattern) : d536 (change p 192 none) = d84 p := by
  change (if p 160 then d525 (change p 192 none) else d535 (change p 192 none)) = d84 p
  rw [sub1556, sub1572]
  rfl
theorem sub1574 (p : Pattern) : d537 (change p 192 none) = d85 p := by
  change (if p 159 then d536 (change p 192 none) else d533 (change p 192 none)) = d85 p
  rw [sub1573, sub1570]
  rfl
theorem sub1575 (p : Pattern) : d538 (change p 192 none) = d162 p := by
  change (if p 158 then d537 (change p 192 none) else d533 (change p 192 none)) = d162 p
  rw [sub1574, sub1570]
  rfl
theorem sub1576 (p : Pattern) : d539 (change p 192 none) = d1060 p := by
  change (if p 168 then d528 (change p 192 none) else d525 (change p 192 none)) = d1060 p
  rw [sub1565, sub1556]
  rfl
theorem sub1577 (p : Pattern) : d540 (change p 192 none) = d1061 p := by
  change (if p 160 then d539 (change p 192 none) else d26 (change p 192 none)) = d1061 p
  rw [sub1576, sub1562]
  rfl
theorem sub1578 (p : Pattern) : d541 (change p 192 none) = d1062 p := by
  change (if p 187 then d528 (change p 192 none) else d25 (change p 192 none)) = d1062 p
  rw [sub1565, sub1561]
  rfl
theorem sub1579 (p : Pattern) : d542 (change p 192 none) = d1063 p := by
  change (if p 186 then d541 (change p 192 none) else d25 (change p 192 none)) = d1063 p
  rw [sub1578, sub1561]
  rfl
theorem sub1580 (p : Pattern) : d543 (change p 192 none) = d1064 p := by
  change (if p 168 then d542 (change p 192 none) else d535 (change p 192 none)) = d1064 p
  rw [sub1579, sub1572]
  rfl
theorem sub1581 (p : Pattern) : d544 (change p 192 none) = d1065 p := by
  change (if p 160 then d539 (change p 192 none) else d543 (change p 192 none)) = d1065 p
  rw [sub1576, sub1580]
  rfl
theorem sub1582 (p : Pattern) : d545 (change p 192 none) = d1066 p := by
  change (if p 159 then d544 (change p 192 none) else d540 (change p 192 none)) = d1066 p
  rw [sub1581, sub1577]
  rfl
theorem sub1583 (p : Pattern) : d546 (change p 192 none) = d1067 p := by
  change (if p 158 then d545 (change p 192 none) else d540 (change p 192 none)) = d1067 p
  rw [sub1582, sub1577]
  rfl
theorem sub1584 (p : Pattern) : d547 (change p 192 none) = d1068 p := by
  change (if p 141 then d546 (change p 192 none) else d538 (change p 192 none)) = d1068 p
  rw [sub1583, sub1575]
  rfl
theorem sub1585 (p : Pattern) : d548 (change p 192 none) = d1069 p := by
  change (if p 134 then d547 (change p 192 none) else d532 (change p 192 none)) = d1069 p
  rw [sub1584, sub1569]
  rfl
theorem sub1586 (p : Pattern) : d549 (change p 192 none) = d48 p := by
  change (if p 158 then d525 (change p 192 none) else d527 (change p 192 none)) = d48 p
  rw [sub1556, sub1558]
  rfl
theorem sub1587 (p : Pattern) : d550 (change p 192 none) = d1070 p := by
  change (if p 158 then d539 (change p 192 none) else d531 (change p 192 none)) = d1070 p
  rw [sub1576, sub1568]
  rfl
theorem sub1588 (p : Pattern) : d551 (change p 192 none) = d1071 p := by
  change (if p 141 then d550 (change p 192 none) else d549 (change p 192 none)) = d1071 p
  rw [sub1587, sub1586]
  rfl
theorem sub1589 (p : Pattern) : d552 (change p 192 none) = d164 p := by
  change (if p 158 then d525 (change p 192 none) else d537 (change p 192 none)) = d164 p
  rw [sub1556, sub1574]
  rfl
theorem sub1590 (p : Pattern) : d553 (change p 192 none) = d1072 p := by
  change (if p 158 then d539 (change p 192 none) else d545 (change p 192 none)) = d1072 p
  rw [sub1576, sub1582]
  rfl
theorem sub1591 (p : Pattern) : d554 (change p 192 none) = d1073 p := by
  change (if p 141 then d553 (change p 192 none) else d552 (change p 192 none)) = d1073 p
  rw [sub1590, sub1589]
  rfl
theorem sub1592 (p : Pattern) : d555 (change p 192 none) = d1074 p := by
  change (if p 134 then d554 (change p 192 none) else d551 (change p 192 none)) = d1074 p
  rw [sub1591, sub1588]
  rfl
theorem sub1593 (p : Pattern) : d556 (change p 192 none) = d1075 p := by
  change (if p 133 then d555 (change p 192 none) else d548 (change p 192 none)) = d1075 p
  rw [sub1592, sub1585]
  rfl
theorem sub1594 (p : Pattern) : d557 (change p 192 none) = d1076 p := by
  change (if p 141 then d539 (change p 192 none) else d525 (change p 192 none)) = d1076 p
  rw [sub1576, sub1556]
  rfl
theorem sub1595 (p : Pattern) : d558 (change p 192 none) = d1077 p := by
  change (if p 133 then d557 (change p 192 none) else d555 (change p 192 none)) = d1077 p
  rw [sub1594, sub1592]
  rfl
theorem sub1596 (p : Pattern) : d559 (change p 192 none) = d1078 p := by
  change (if p 132 then d558 (change p 192 none) else d556 (change p 192 none)) = d1078 p
  rw [sub1595, sub1593]
  rfl
theorem sub1597 (p : Pattern) : d560 (change p 192 none) = d92 p := by
  change (if p 186 then d525 (change p 192 none) else d534 (change p 192 none)) = d92 p
  rw [sub1556, sub1571]
  rfl
theorem sub1598 (p : Pattern) : d561 (change p 192 none) = d94 p := by
  change (if p 160 then d560 (change p 192 none) else d535 (change p 192 none)) = d94 p
  rw [sub1597, sub1572]
  rfl
theorem sub1599 (p : Pattern) : d562 (change p 192 none) = d100 p := by
  change (if p 159 then d561 (change p 192 none) else d527 (change p 192 none)) = d100 p
  rw [sub1598, sub1558]
  rfl
theorem sub1600 (p : Pattern) : d563 (change p 192 none) = d169 p := by
  change (if p 158 then d562 (change p 192 none) else d527 (change p 192 none)) = d169 p
  rw [sub1599, sub1558]
  rfl
theorem sub1601 (p : Pattern) : d564 (change p 192 none) = d1079 p := by
  change (if p 186 then d528 (change p 192 none) else d541 (change p 192 none)) = d1079 p
  rw [sub1565, sub1578]
  rfl
theorem sub1602 (p : Pattern) : d565 (change p 192 none) = d1080 p := by
  change (if p 168 then d564 (change p 192 none) else d560 (change p 192 none)) = d1080 p
  rw [sub1601, sub1597]
  rfl
theorem sub1603 (p : Pattern) : d566 (change p 192 none) = d1081 p := by
  change (if p 160 then d565 (change p 192 none) else d543 (change p 192 none)) = d1081 p
  rw [sub1602, sub1580]
  rfl
theorem sub1604 (p : Pattern) : d567 (change p 192 none) = d1082 p := by
  change (if p 159 then d566 (change p 192 none) else d531 (change p 192 none)) = d1082 p
  rw [sub1603, sub1568]
  rfl
theorem sub1605 (p : Pattern) : d568 (change p 192 none) = d1083 p := by
  change (if p 158 then d567 (change p 192 none) else d531 (change p 192 none)) = d1083 p
  rw [sub1604, sub1568]
  rfl
theorem sub1606 (p : Pattern) : d569 (change p 192 none) = d1084 p := by
  change (if p 141 then d568 (change p 192 none) else d563 (change p 192 none)) = d1084 p
  rw [sub1605, sub1600]
  rfl
theorem sub1607 (p : Pattern) : d570 (change p 192 none) = d1085 p := by
  change (if p 134 then d557 (change p 192 none) else d569 (change p 192 none)) = d1085 p
  rw [sub1594, sub1606]
  rfl
theorem sub1608 (p : Pattern) : d571 (change p 192 none) = d93 p := by
  change (if p 160 then d560 (change p 192 none) else d24 (change p 192 none)) = d93 p
  rw [sub1597, sub1554]
  rfl
theorem sub1609 (p : Pattern) : d572 (change p 192 none) = d95 p := by
  change (if p 159 then d561 (change p 192 none) else d571 (change p 192 none)) = d95 p
  rw [sub1598, sub1608]
  rfl
theorem sub1610 (p : Pattern) : d573 (change p 192 none) = d171 p := by
  change (if p 158 then d525 (change p 192 none) else d572 (change p 192 none)) = d171 p
  rw [sub1556, sub1609]
  rfl
theorem sub1611 (p : Pattern) : d574 (change p 192 none) = d1086 p := by
  change (if p 160 then d565 (change p 192 none) else d26 (change p 192 none)) = d1086 p
  rw [sub1602, sub1562]
  rfl
theorem sub1612 (p : Pattern) : d575 (change p 192 none) = d1087 p := by
  change (if p 159 then d566 (change p 192 none) else d574 (change p 192 none)) = d1087 p
  rw [sub1603, sub1611]
  rfl
theorem sub1613 (p : Pattern) : d576 (change p 192 none) = d1088 p := by
  change (if p 158 then d539 (change p 192 none) else d575 (change p 192 none)) = d1088 p
  rw [sub1576, sub1612]
  rfl
theorem sub1614 (p : Pattern) : d577 (change p 192 none) = d1089 p := by
  change (if p 141 then d576 (change p 192 none) else d573 (change p 192 none)) = d1089 p
  rw [sub1613, sub1610]
  rfl
theorem sub1615 (p : Pattern) : d578 (change p 192 none) = d1090 p := by
  change (if p 134 then d557 (change p 192 none) else d577 (change p 192 none)) = d1090 p
  rw [sub1594, sub1614]
  rfl
theorem sub1616 (p : Pattern) : d579 (change p 192 none) = d1091 p := by
  change (if p 133 then d578 (change p 192 none) else d570 (change p 192 none)) = d1091 p
  rw [sub1615, sub1607]
  rfl
theorem sub1617 (p : Pattern) : d580 (change p 192 none) = d174 p := by
  change (if p 158 then d525 (change p 192 none) else d562 (change p 192 none)) = d174 p
  rw [sub1556, sub1599]
  rfl
theorem sub1618 (p : Pattern) : d581 (change p 192 none) = d1092 p := by
  change (if p 158 then d539 (change p 192 none) else d567 (change p 192 none)) = d1092 p
  rw [sub1576, sub1604]
  rfl
theorem sub1619 (p : Pattern) : d582 (change p 192 none) = d1093 p := by
  change (if p 141 then d581 (change p 192 none) else d580 (change p 192 none)) = d1093 p
  rw [sub1618, sub1617]
  rfl
theorem sub1620 (p : Pattern) : d583 (change p 192 none) = d1094 p := by
  change (if p 134 then d557 (change p 192 none) else d582 (change p 192 none)) = d1094 p
  rw [sub1594, sub1619]
  rfl
theorem sub1621 (p : Pattern) : d584 (change p 192 none) = d1095 p := by
  change (if p 133 then d557 (change p 192 none) else d583 (change p 192 none)) = d1095 p
  rw [sub1594, sub1620]
  rfl
theorem sub1622 (p : Pattern) : d585 (change p 192 none) = d1096 p := by
  change (if p 132 then d584 (change p 192 none) else d579 (change p 192 none)) = d1096 p
  rw [sub1621, sub1616]
  rfl
theorem sub1623 (p : Pattern) : d586 (change p 192 none) = d1097 p := by
  change (if p 108 then d585 (change p 192 none) else d559 (change p 192 none)) = d1097 p
  rw [sub1622, sub1596]
  rfl
theorem sub1624 (p : Pattern) : d1 (change p 10000 (some 168)) = d1 p := by
  rfl
theorem sub1625 (p : Pattern) : d8 (change p 10000 (some 168)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 168)) else d0 (change p 10000 (some 168))) = d8 p
  rw [sub1624, sub286]
  rfl
theorem sub1626 (p : Pattern) : d3 (change p 10000 (some 168)) = d3 p := by
  rfl
theorem sub1627 (p : Pattern) : d9 (change p 10000 (some 168)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 168)) else d2 (change p 10000 (some 168))) = d9 p
  rw [sub1626, sub287]
  rfl
theorem sub1628 (p : Pattern) : d10 (change p 10000 (some 168)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 168)) else d8 (change p 10000 (some 168))) = d10 p
  rw [sub1627, sub1625]
  rfl
theorem sub1629 (p : Pattern) : d11 (change p 10000 (some 168)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 168)) else d8 (change p 10000 (some 168))) = d11 p
  rw [sub1628, sub1625]
  rfl
theorem sub1630 (p : Pattern) : d12 (change p 10000 (some 168)) = d11 p := by
  change d11 (change p 10000 (some 168)) = d11 p
  exact sub1629 p
theorem sub1631 (p : Pattern) : d5 (change p 10000 (some 168)) = d5 p := by
  rfl
theorem sub1632 (p : Pattern) : d58 (change p 10000 (some 168)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 168)) else d4 (change p 10000 (some 168))) = d58 p
  rw [sub1631, sub290]
  rfl
theorem sub1633 (p : Pattern) : d59 (change p 10000 (some 168)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 168)) else d9 (change p 10000 (some 168))) = d59 p
  rw [sub1632, sub1627]
  rfl
theorem sub1634 (p : Pattern) : d60 (change p 10000 (some 168)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 168)) else d9 (change p 10000 (some 168))) = d60 p
  rw [sub1633, sub1627]
  rfl
theorem sub1635 (p : Pattern) : d61 (change p 10000 (some 168)) = d61 p := by
  change (if p 186 then d60 (change p 10000 (some 168)) else d11 (change p 10000 (some 168))) = d61 p
  rw [sub1634, sub1629]
  rfl
theorem sub1636 (p : Pattern) : d62 (change p 10000 (some 168)) = d61 p := by
  change d61 (change p 10000 (some 168)) = d61 p
  exact sub1635 p
theorem sub1637 (p : Pattern) : d63 (change p 10000 (some 168)) = d1098 p := by
  change (if p 160 then d62 (change p 10000 (some 168)) else d12 (change p 10000 (some 168))) = d1098 p
  rw [sub1636, sub1630]
  rfl
theorem sub1638 (p : Pattern) : d64 (change p 10000 (some 168)) = d1099 p := by
  change (if p 141 then d63 (change p 10000 (some 168)) else d57 (change p 10000 (some 168))) = d1099 p
  rw [sub1637, sub294]
  rfl
theorem sub1639 (p : Pattern) : d65 (change p 10000 (some 168)) = d60 p := by
  change d60 (change p 10000 (some 168)) = d60 p
  exact sub1634 p
theorem sub1640 (p : Pattern) : d109 (change p 10000 (some 168)) = d1100 p := by
  change (if p 160 then d65 (change p 10000 (some 168)) else d12 (change p 10000 (some 168))) = d1100 p
  rw [sub1639, sub1630]
  rfl
theorem sub1641 (p : Pattern) : d125 (change p 10000 (some 168)) = d125 p := by
  change (if p 187 then d60 (change p 10000 (some 168)) else d11 (change p 10000 (some 168))) = d125 p
  rw [sub1634, sub1629]
  rfl
theorem sub1642 (p : Pattern) : d126 (change p 10000 (some 168)) = d126 p := by
  change (if p 186 then d125 (change p 10000 (some 168)) else d11 (change p 10000 (some 168))) = d126 p
  rw [sub1641, sub1629]
  rfl
theorem sub1643 (p : Pattern) : d127 (change p 10000 (some 168)) = d126 p := by
  change d126 (change p 10000 (some 168)) = d126 p
  exact sub1642 p
theorem sub1644 (p : Pattern) : d128 (change p 10000 (some 168)) = d1101 p := by
  change (if p 160 then d65 (change p 10000 (some 168)) else d127 (change p 10000 (some 168))) = d1101 p
  rw [sub1639, sub1643]
  rfl
theorem sub1645 (p : Pattern) : d129 (change p 10000 (some 168)) = d1102 p := by
  change (if p 159 then d128 (change p 10000 (some 168)) else d109 (change p 10000 (some 168))) = d1102 p
  rw [sub1644, sub1640]
  rfl
theorem sub1646 (p : Pattern) : d237 (change p 10000 (some 168)) = d1103 p := by
  change (if p 158 then d129 (change p 10000 (some 168)) else d109 (change p 10000 (some 168))) = d1103 p
  rw [sub1645, sub1640]
  rfl
theorem sub1647 (p : Pattern) : d238 (change p 10000 (some 168)) = d1104 p := by
  change (if p 141 then d237 (change p 10000 (some 168)) else d179 (change p 10000 (some 168))) = d1104 p
  rw [sub1646, sub300]
  rfl
theorem sub1648 (p : Pattern) : d239 (change p 10000 (some 168)) = d1105 p := by
  change (if p 134 then d238 (change p 10000 (some 168)) else d64 (change p 10000 (some 168))) = d1105 p
  rw [sub1647, sub1638]
  rfl
theorem sub1649 (p : Pattern) : d69 (change p 10000 (some 168)) = d1106 p := by
  change (if p 158 then d65 (change p 10000 (some 168)) else d63 (change p 10000 (some 168))) = d1106 p
  rw [sub1639, sub1637]
  rfl
theorem sub1650 (p : Pattern) : d70 (change p 10000 (some 168)) = d1107 p := by
  change (if p 141 then d69 (change p 10000 (some 168)) else d68 (change p 10000 (some 168))) = d1107 p
  rw [sub1649, sub302]
  rfl
theorem sub1651 (p : Pattern) : d240 (change p 10000 (some 168)) = d1108 p := by
  change (if p 158 then d65 (change p 10000 (some 168)) else d129 (change p 10000 (some 168))) = d1108 p
  rw [sub1639, sub1645]
  rfl
theorem sub1652 (p : Pattern) : d241 (change p 10000 (some 168)) = d1109 p := by
  change (if p 141 then d240 (change p 10000 (some 168)) else d181 (change p 10000 (some 168))) = d1109 p
  rw [sub1651, sub303]
  rfl
theorem sub1653 (p : Pattern) : d242 (change p 10000 (some 168)) = d1110 p := by
  change (if p 134 then d241 (change p 10000 (some 168)) else d70 (change p 10000 (some 168))) = d1110 p
  rw [sub1652, sub1650]
  rfl
theorem sub1654 (p : Pattern) : d243 (change p 10000 (some 168)) = d1111 p := by
  change (if p 133 then d242 (change p 10000 (some 168)) else d239 (change p 10000 (some 168))) = d1111 p
  rw [sub1653, sub1648]
  rfl
theorem sub1655 (p : Pattern) : d66 (change p 10000 (some 168)) = d1112 p := by
  change (if p 141 then d65 (change p 10000 (some 168)) else d55 (change p 10000 (some 168))) = d1112 p
  rw [sub1639, sub292]
  rfl
theorem sub1656 (p : Pattern) : d244 (change p 10000 (some 168)) = d1113 p := by
  change (if p 133 then d66 (change p 10000 (some 168)) else d242 (change p 10000 (some 168))) = d1113 p
  rw [sub1655, sub1653]
  rfl
theorem sub1657 (p : Pattern) : d245 (change p 10000 (some 168)) = d1114 p := by
  change (if p 132 then d244 (change p 10000 (some 168)) else d243 (change p 10000 (some 168))) = d1114 p
  rw [sub1656, sub1654]
  rfl
theorem sub1658 (p : Pattern) : d143 (change p 10000 (some 168)) = d143 p := by
  change (if p 186 then d60 (change p 10000 (some 168)) else d125 (change p 10000 (some 168))) = d143 p
  rw [sub1634, sub1641]
  rfl
theorem sub1659 (p : Pattern) : d144 (change p 10000 (some 168)) = d143 p := by
  change d143 (change p 10000 (some 168)) = d143 p
  exact sub1658 p
theorem sub1660 (p : Pattern) : d146 (change p 10000 (some 168)) = d1115 p := by
  change (if p 160 then d144 (change p 10000 (some 168)) else d127 (change p 10000 (some 168))) = d1115 p
  rw [sub1659, sub1643]
  rfl
theorem sub1661 (p : Pattern) : d155 (change p 10000 (some 168)) = d1116 p := by
  change (if p 159 then d146 (change p 10000 (some 168)) else d63 (change p 10000 (some 168))) = d1116 p
  rw [sub1660, sub1637]
  rfl
theorem sub1662 (p : Pattern) : d246 (change p 10000 (some 168)) = d1117 p := by
  change (if p 158 then d155 (change p 10000 (some 168)) else d63 (change p 10000 (some 168))) = d1117 p
  rw [sub1661, sub1637]
  rfl
theorem sub1663 (p : Pattern) : d247 (change p 10000 (some 168)) = d1118 p := by
  change (if p 141 then d246 (change p 10000 (some 168)) else d186 (change p 10000 (some 168))) = d1118 p
  rw [sub1662, sub311]
  rfl
theorem sub1664 (p : Pattern) : d248 (change p 10000 (some 168)) = d1119 p := by
  change (if p 134 then d66 (change p 10000 (some 168)) else d247 (change p 10000 (some 168))) = d1119 p
  rw [sub1655, sub1663]
  rfl
theorem sub1665 (p : Pattern) : d145 (change p 10000 (some 168)) = d1120 p := by
  change (if p 160 then d144 (change p 10000 (some 168)) else d12 (change p 10000 (some 168))) = d1120 p
  rw [sub1659, sub1630]
  rfl
theorem sub1666 (p : Pattern) : d147 (change p 10000 (some 168)) = d1121 p := by
  change (if p 159 then d146 (change p 10000 (some 168)) else d145 (change p 10000 (some 168))) = d1121 p
  rw [sub1660, sub1665]
  rfl
theorem sub1667 (p : Pattern) : d249 (change p 10000 (some 168)) = d1122 p := by
  change (if p 158 then d65 (change p 10000 (some 168)) else d147 (change p 10000 (some 168))) = d1122 p
  rw [sub1639, sub1666]
  rfl
theorem sub1668 (p : Pattern) : d250 (change p 10000 (some 168)) = d1123 p := by
  change (if p 141 then d249 (change p 10000 (some 168)) else d188 (change p 10000 (some 168))) = d1123 p
  rw [sub1667, sub315]
  rfl
theorem sub1669 (p : Pattern) : d251 (change p 10000 (some 168)) = d1124 p := by
  change (if p 134 then d66 (change p 10000 (some 168)) else d250 (change p 10000 (some 168))) = d1124 p
  rw [sub1655, sub1668]
  rfl
theorem sub1670 (p : Pattern) : d252 (change p 10000 (some 168)) = d1125 p := by
  change (if p 133 then d251 (change p 10000 (some 168)) else d248 (change p 10000 (some 168))) = d1125 p
  rw [sub1669, sub1664]
  rfl
theorem sub1671 (p : Pattern) : d253 (change p 10000 (some 168)) = d1126 p := by
  change (if p 158 then d65 (change p 10000 (some 168)) else d155 (change p 10000 (some 168))) = d1126 p
  rw [sub1639, sub1661]
  rfl
theorem sub1672 (p : Pattern) : d254 (change p 10000 (some 168)) = d1127 p := by
  change (if p 141 then d253 (change p 10000 (some 168)) else d191 (change p 10000 (some 168))) = d1127 p
  rw [sub1671, sub318]
  rfl
theorem sub1673 (p : Pattern) : d255 (change p 10000 (some 168)) = d1128 p := by
  change (if p 134 then d66 (change p 10000 (some 168)) else d254 (change p 10000 (some 168))) = d1128 p
  rw [sub1655, sub1672]
  rfl
theorem sub1674 (p : Pattern) : d256 (change p 10000 (some 168)) = d1129 p := by
  change (if p 133 then d66 (change p 10000 (some 168)) else d255 (change p 10000 (some 168))) = d1129 p
  rw [sub1655, sub1673]
  rfl
theorem sub1675 (p : Pattern) : d257 (change p 10000 (some 168)) = d1130 p := by
  change (if p 132 then d256 (change p 10000 (some 168)) else d252 (change p 10000 (some 168))) = d1130 p
  rw [sub1674, sub1670]
  rfl
theorem sub1676 (p : Pattern) : d258 (change p 10000 (some 168)) = d1131 p := by
  change (if p 108 then d257 (change p 10000 (some 168)) else d245 (change p 10000 (some 168))) = d1131 p
  rw [sub1675, sub1657]
  rfl
theorem sub1677 (p : Pattern) : d0 (change p 193 none) = d0 p := by
  rfl
theorem sub1678 (p : Pattern) : d6 (change p 193 none) = d0 p := by
  change d0 (change p 193 none) = d0 p
  exact sub1677 p
theorem sub1679 (p : Pattern) : d28 (change p 193 none) = d0 p := by
  change d0 (change p 193 none) = d0 p
  exact sub1677 p
end NetHack.Sokoban12CostPartition
