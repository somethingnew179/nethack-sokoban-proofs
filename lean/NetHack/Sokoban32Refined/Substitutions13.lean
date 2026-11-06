/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1560 (p : Pattern) : d32 (change p 106 (some 80)) = d32 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d30 (change p 106 (some 80))) = d32 p
  rw [sub1529, sub1558]
  rfl
theorem sub1561 (p : Pattern) : d33 (change p 106 (some 80)) = d33 p := by
  change (if p 158 then d32 (change p 106 (some 80)) else d31 (change p 106 (some 80))) = d33 p
  rw [sub1560, sub1559]
  rfl
theorem sub1562 (p : Pattern) : d34 (change p 106 (some 80)) = d34 p := by
  change (if p 139 then d24 (change p 106 (some 80)) else d33 (change p 106 (some 80))) = d34 p
  rw [sub1552, sub1561]
  rfl
theorem sub1563 (p : Pattern) : d35 (change p 106 (some 80)) = d35 p := by
  change (if p 138 then d34 (change p 106 (some 80)) else d33 (change p 106 (some 80))) = d35 p
  rw [sub1562, sub1561]
  rfl
theorem sub1564 (p : Pattern) : d36 (change p 106 (some 80)) = d36 p := by
  change (if p 134 then d35 (change p 106 (some 80)) else d16 (change p 106 (some 80))) = d36 p
  rw [sub1563, sub1544]
  rfl
theorem sub1565 (p : Pattern) : d37 (change p 106 (some 80)) = d37 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d5 (change p 106 (some 80))) = d37 p
  rw [sub1529, sub1532]
  rfl
theorem sub1566 (p : Pattern) : d38 (change p 106 (some 80)) = d38 p := by
  change (if p 158 then d37 (change p 106 (some 80)) else d6 (change p 106 (some 80))) = d38 p
  rw [sub1565, sub1533]
  rfl
theorem sub1567 (p : Pattern) : d39 (change p 106 (some 80)) = d39 p := by
  change (if p 159 then d2 (change p 106 (some 80)) else d11 (change p 106 (some 80))) = d39 p
  rw [sub1529, sub1539]
  rfl
theorem sub1568 (p : Pattern) : d40 (change p 106 (some 80)) = d40 p := by
  change (if p 158 then d39 (change p 106 (some 80)) else d12 (change p 106 (some 80))) = d40 p
  rw [sub1567, sub1540]
  rfl
theorem sub1569 (p : Pattern) : d41 (change p 106 (some 80)) = d41 p := by
  change (if p 139 then d40 (change p 106 (some 80)) else d38 (change p 106 (some 80))) = d41 p
  rw [sub1568, sub1566]
  rfl
theorem sub1570 (p : Pattern) : d42 (change p 106 (some 80)) = d42 p := by
  change (if p 138 then d41 (change p 106 (some 80)) else d38 (change p 106 (some 80))) = d42 p
  rw [sub1569, sub1566]
  rfl
theorem sub1571 (p : Pattern) : d43 (change p 106 (some 80)) = d43 p := by
  change (if p 134 then d26 (change p 106 (some 80)) else d42 (change p 106 (some 80))) = d43 p
  rw [sub1554, sub1570]
  rfl
theorem sub1572 (p : Pattern) : d44 (change p 106 (some 80)) = d44 p := by
  change (if p 133 then d43 (change p 106 (some 80)) else d36 (change p 106 (some 80))) = d44 p
  rw [sub1571, sub1564]
  rfl
theorem sub1573 (p : Pattern) : d45 (change p 106 (some 80)) = d45 p := by
  change (if p 132 then d44 (change p 106 (some 80)) else d28 (change p 106 (some 80))) = d45 p
  rw [sub1572, sub1556]
  rfl
theorem sub1574 (p : Pattern) : d46 (change p 106 (some 80)) = d46 p := by
  change (if p 134 then d25 (change p 106 (some 80)) else d15 (change p 106 (some 80))) = d46 p
  rw [sub1553, sub1543]
  rfl
theorem sub1575 (p : Pattern) : d47 (change p 106 (some 80)) = d47 p := by
  change (if p 133 then d46 (change p 106 (some 80)) else d15 (change p 106 (some 80))) = d47 p
  rw [sub1574, sub1543]
  rfl
theorem sub1576 (p : Pattern) : d48 (change p 106 (some 80)) = d48 p := by
  change (if p 134 then d34 (change p 106 (some 80)) else d15 (change p 106 (some 80))) = d48 p
  rw [sub1562, sub1543]
  rfl
theorem sub1577 (p : Pattern) : d49 (change p 106 (some 80)) = d49 p := by
  change (if p 134 then d25 (change p 106 (some 80)) else d41 (change p 106 (some 80))) = d49 p
  rw [sub1553, sub1569]
  rfl
theorem sub1578 (p : Pattern) : d50 (change p 106 (some 80)) = d50 p := by
  change (if p 133 then d49 (change p 106 (some 80)) else d48 (change p 106 (some 80))) = d50 p
  rw [sub1577, sub1576]
  rfl
theorem sub1579 (p : Pattern) : d51 (change p 106 (some 80)) = d51 p := by
  change (if p 132 then d50 (change p 106 (some 80)) else d47 (change p 106 (some 80))) = d51 p
  rw [sub1578, sub1575]
  rfl
theorem sub1580 (p : Pattern) : d52 (change p 106 (some 80)) = d52 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d8 (change p 106 (some 80))) = d52 p
  rw [sub1529, sub1535]
  rfl
theorem sub1581 (p : Pattern) : d53 (change p 106 (some 80)) = d53 p := by
  change (if p 138 then d52 (change p 106 (some 80)) else d15 (change p 106 (some 80))) = d53 p
  rw [sub1580, sub1543]
  rfl
theorem sub1582 (p : Pattern) : d54 (change p 106 (some 80)) = d54 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d20 (change p 106 (some 80))) = d54 p
  rw [sub1529, sub1548]
  rfl
theorem sub1583 (p : Pattern) : d55 (change p 106 (some 80)) = d55 p := by
  change (if p 138 then d54 (change p 106 (some 80)) else d25 (change p 106 (some 80))) = d55 p
  rw [sub1582, sub1553]
  rfl
theorem sub1584 (p : Pattern) : d56 (change p 106 (some 80)) = d56 p := by
  change (if p 134 then d55 (change p 106 (some 80)) else d53 (change p 106 (some 80))) = d56 p
  rw [sub1583, sub1581]
  rfl
theorem sub1585 (p : Pattern) : d57 (change p 106 (some 80)) = d57 p := by
  change (if p 133 then d56 (change p 106 (some 80)) else d53 (change p 106 (some 80))) = d57 p
  rw [sub1584, sub1581]
  rfl
theorem sub1586 (p : Pattern) : d58 (change p 106 (some 80)) = d58 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d33 (change p 106 (some 80))) = d58 p
  rw [sub1529, sub1561]
  rfl
theorem sub1587 (p : Pattern) : d59 (change p 106 (some 80)) = d59 p := by
  change (if p 138 then d58 (change p 106 (some 80)) else d34 (change p 106 (some 80))) = d59 p
  rw [sub1586, sub1562]
  rfl
theorem sub1588 (p : Pattern) : d60 (change p 106 (some 80)) = d60 p := by
  change (if p 134 then d59 (change p 106 (some 80)) else d53 (change p 106 (some 80))) = d60 p
  rw [sub1587, sub1581]
  rfl
theorem sub1589 (p : Pattern) : d61 (change p 106 (some 80)) = d61 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d38 (change p 106 (some 80))) = d61 p
  rw [sub1529, sub1566]
  rfl
theorem sub1590 (p : Pattern) : d62 (change p 106 (some 80)) = d62 p := by
  change (if p 138 then d61 (change p 106 (some 80)) else d41 (change p 106 (some 80))) = d62 p
  rw [sub1589, sub1569]
  rfl
theorem sub1591 (p : Pattern) : d63 (change p 106 (some 80)) = d63 p := by
  change (if p 134 then d55 (change p 106 (some 80)) else d62 (change p 106 (some 80))) = d63 p
  rw [sub1583, sub1590]
  rfl
theorem sub1592 (p : Pattern) : d64 (change p 106 (some 80)) = d64 p := by
  change (if p 133 then d63 (change p 106 (some 80)) else d60 (change p 106 (some 80))) = d64 p
  rw [sub1591, sub1588]
  rfl
theorem sub1593 (p : Pattern) : d65 (change p 106 (some 80)) = d65 p := by
  change (if p 132 then d64 (change p 106 (some 80)) else d57 (change p 106 (some 80))) = d65 p
  rw [sub1592, sub1585]
  rfl
theorem sub1594 (p : Pattern) : d66 (change p 106 (some 80)) = d66 p := by
  change (if p 113 then d65 (change p 106 (some 80)) else d51 (change p 106 (some 80))) = d66 p
  rw [sub1593, sub1579]
  rfl
theorem sub1595 (p : Pattern) : d67 (change p 106 (some 80)) = d67 p := by
  change (if p 112 then d66 (change p 106 (some 80)) else d45 (change p 106 (some 80))) = d67 p
  rw [sub1594, sub1573]
  rfl
theorem sub1596 (p : Pattern) : d180 (change p 106 (some 80)) = d67 p := by
  change d67 (change p 106 (some 80)) = d67 p
  exact sub1595 p
theorem sub1597 (p : Pattern) : d86 (change p 106 (some 80)) = d86 p := by
  change (if p 138 then d52 (change p 106 (some 80)) else d8 (change p 106 (some 80))) = d86 p
  rw [sub1580, sub1535]
  rfl
theorem sub1598 (p : Pattern) : d87 (change p 106 (some 80)) = d87 p := by
  change (if p 138 then d54 (change p 106 (some 80)) else d20 (change p 106 (some 80))) = d87 p
  rw [sub1582, sub1548]
  rfl
theorem sub1599 (p : Pattern) : d88 (change p 106 (some 80)) = d88 p := by
  change (if p 134 then d87 (change p 106 (some 80)) else d86 (change p 106 (some 80))) = d88 p
  rw [sub1598, sub1597]
  rfl
theorem sub1600 (p : Pattern) : d89 (change p 106 (some 80)) = d89 p := by
  change (if p 133 then d88 (change p 106 (some 80)) else d86 (change p 106 (some 80))) = d89 p
  rw [sub1599, sub1597]
  rfl
theorem sub1601 (p : Pattern) : d119 (change p 106 (some 80)) = d119 p := by
  change (if p 139 then d20 (change p 106 (some 80)) else d33 (change p 106 (some 80))) = d119 p
  rw [sub1548, sub1561]
  rfl
theorem sub1602 (p : Pattern) : d120 (change p 106 (some 80)) = d120 p := by
  change (if p 138 then d58 (change p 106 (some 80)) else d119 (change p 106 (some 80))) = d120 p
  rw [sub1586, sub1601]
  rfl
theorem sub1603 (p : Pattern) : d121 (change p 106 (some 80)) = d121 p := by
  change (if p 134 then d120 (change p 106 (some 80)) else d86 (change p 106 (some 80))) = d121 p
  rw [sub1602, sub1597]
  rfl
theorem sub1604 (p : Pattern) : d92 (change p 106 (some 80)) = d92 p := by
  change (if p 138 then d61 (change p 106 (some 80)) else d38 (change p 106 (some 80))) = d92 p
  rw [sub1589, sub1566]
  rfl
theorem sub1605 (p : Pattern) : d93 (change p 106 (some 80)) = d93 p := by
  change (if p 134 then d87 (change p 106 (some 80)) else d92 (change p 106 (some 80))) = d93 p
  rw [sub1598, sub1604]
  rfl
theorem sub1606 (p : Pattern) : d122 (change p 106 (some 80)) = d122 p := by
  change (if p 133 then d93 (change p 106 (some 80)) else d121 (change p 106 (some 80))) = d122 p
  rw [sub1605, sub1603]
  rfl
theorem sub1607 (p : Pattern) : d123 (change p 106 (some 80)) = d123 p := by
  change (if p 132 then d122 (change p 106 (some 80)) else d89 (change p 106 (some 80))) = d123 p
  rw [sub1606, sub1600]
  rfl
theorem sub1608 (p : Pattern) : d124 (change p 106 (some 80)) = d124 p := by
  change (if p 113 then d123 (change p 106 (some 80)) else d45 (change p 106 (some 80))) = d124 p
  rw [sub1607, sub1573]
  rfl
theorem sub1609 (p : Pattern) : d97 (change p 106 (some 80)) = d97 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d14 (change p 106 (some 80))) = d97 p
  rw [sub1529, sub1542]
  rfl
theorem sub1610 (p : Pattern) : d98 (change p 106 (some 80)) = d98 p := by
  change (if p 138 then d97 (change p 106 (some 80)) else d14 (change p 106 (some 80))) = d98 p
  rw [sub1609, sub1542]
  rfl
theorem sub1611 (p : Pattern) : d70 (change p 106 (some 80)) = d70 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d24 (change p 106 (some 80))) = d70 p
  rw [sub1529, sub1552]
  rfl
theorem sub1612 (p : Pattern) : d71 (change p 106 (some 80)) = d71 p := by
  change (if p 138 then d70 (change p 106 (some 80)) else d24 (change p 106 (some 80))) = d71 p
  rw [sub1611, sub1552]
  rfl
theorem sub1613 (p : Pattern) : d99 (change p 106 (some 80)) = d99 p := by
  change (if p 134 then d71 (change p 106 (some 80)) else d98 (change p 106 (some 80))) = d99 p
  rw [sub1612, sub1610]
  rfl
theorem sub1614 (p : Pattern) : d100 (change p 106 (some 80)) = d100 p := by
  change (if p 133 then d99 (change p 106 (some 80)) else d98 (change p 106 (some 80))) = d100 p
  rw [sub1613, sub1610]
  rfl
theorem sub1615 (p : Pattern) : d68 (change p 106 (some 80)) = d68 p := by
  change (if p 139 then d2 (change p 106 (some 80)) else d40 (change p 106 (some 80))) = d68 p
  rw [sub1529, sub1568]
  rfl
theorem sub1616 (p : Pattern) : d69 (change p 106 (some 80)) = d69 p := by
  change (if p 138 then d68 (change p 106 (some 80)) else d40 (change p 106 (some 80))) = d69 p
  rw [sub1615, sub1568]
  rfl
theorem sub1617 (p : Pattern) : d72 (change p 106 (some 80)) = d72 p := by
  change (if p 134 then d71 (change p 106 (some 80)) else d69 (change p 106 (some 80))) = d72 p
  rw [sub1612, sub1616]
  rfl
theorem sub1618 (p : Pattern) : d101 (change p 106 (some 80)) = d101 p := by
  change (if p 133 then d72 (change p 106 (some 80)) else d99 (change p 106 (some 80))) = d101 p
  rw [sub1617, sub1613]
  rfl
theorem sub1619 (p : Pattern) : d102 (change p 106 (some 80)) = d102 p := by
  change (if p 132 then d101 (change p 106 (some 80)) else d100 (change p 106 (some 80))) = d102 p
  rw [sub1618, sub1614]
  rfl
theorem sub1620 (p : Pattern) : d109 (change p 106 (some 80)) = d109 p := by
  change (if p 134 then d70 (change p 106 (some 80)) else d97 (change p 106 (some 80))) = d109 p
  rw [sub1611, sub1609]
  rfl
theorem sub1621 (p : Pattern) : d110 (change p 106 (some 80)) = d110 p := by
  change (if p 133 then d109 (change p 106 (some 80)) else d97 (change p 106 (some 80))) = d110 p
  rw [sub1620, sub1609]
  rfl
theorem sub1622 (p : Pattern) : d75 (change p 106 (some 80)) = d75 p := by
  change (if p 134 then d70 (change p 106 (some 80)) else d68 (change p 106 (some 80))) = d75 p
  rw [sub1611, sub1615]
  rfl
theorem sub1623 (p : Pattern) : d125 (change p 106 (some 80)) = d125 p := by
  change (if p 133 then d75 (change p 106 (some 80)) else d109 (change p 106 (some 80))) = d125 p
  rw [sub1622, sub1620]
  rfl
theorem sub1624 (p : Pattern) : d126 (change p 106 (some 80)) = d126 p := by
  change (if p 132 then d125 (change p 106 (some 80)) else d110 (change p 106 (some 80))) = d126 p
  rw [sub1623, sub1621]
  rfl
theorem sub1625 (p : Pattern) : d127 (change p 106 (some 80)) = d127 p := by
  change (if p 113 then d126 (change p 106 (some 80)) else d102 (change p 106 (some 80))) = d127 p
  rw [sub1624, sub1619]
  rfl
theorem sub1626 (p : Pattern) : d128 (change p 106 (some 80)) = d128 p := by
  change (if p 112 then d127 (change p 106 (some 80)) else d124 (change p 106 (some 80))) = d128 p
  rw [sub1625, sub1608]
  rfl
theorem sub1627 (p : Pattern) : d181 (change p 106 (some 80)) = d128 p := by
  change d128 (change p 106 (some 80)) = d128 p
  exact sub1626 p
theorem sub1628 (p : Pattern) : d182 (change p 106 (some 80)) = d1147 p := by
  change (if p 86 then d181 (change p 106 (some 80)) else d180 (change p 106 (some 80))) = d1147 p
  rw [sub1627, sub1596]
  rfl
theorem sub1629 (p : Pattern) : d183 (change p 106 (some 80)) = d1147 p := by
  change d182 (change p 106 (some 80)) = d1147 p
  exact sub1628 p
theorem sub1630 (p : Pattern) : d0 (change p 133 (some 134)) = d0 p := by
  rfl
theorem sub1631 (p : Pattern) : d2 (change p 133 (some 134)) = d2 p := by
  rfl
theorem sub1632 (p : Pattern) : d3 (change p 133 (some 134)) = d3 p := by
  change (if p 161 then d2 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d3 p
  rw [sub1631, sub1630]
  rfl
theorem sub1633 (p : Pattern) : d4 (change p 133 (some 134)) = d4 p := by
  change (if p 160 then d3 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d4 p
  rw [sub1632, sub1630]
  rfl
theorem sub1634 (p : Pattern) : d5 (change p 133 (some 134)) = d5 p := by
  change (if p 160 then d2 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d5 p
  rw [sub1631, sub1630]
  rfl
theorem sub1635 (p : Pattern) : d6 (change p 133 (some 134)) = d6 p := by
  change (if p 159 then d5 (change p 133 (some 134)) else d4 (change p 133 (some 134))) = d6 p
  rw [sub1634, sub1633]
  rfl
theorem sub1636 (p : Pattern) : d7 (change p 133 (some 134)) = d7 p := by
  change (if p 159 then d2 (change p 133 (some 134)) else d4 (change p 133 (some 134))) = d7 p
  rw [sub1631, sub1633]
  rfl
theorem sub1637 (p : Pattern) : d8 (change p 133 (some 134)) = d8 p := by
  change (if p 158 then d7 (change p 133 (some 134)) else d6 (change p 133 (some 134))) = d8 p
  rw [sub1636, sub1635]
  rfl
theorem sub1638 (p : Pattern) : d1 (change p 133 (some 134)) = d1 p := by
  rfl
theorem sub1639 (p : Pattern) : d9 (change p 133 (some 134)) = d9 p := by
  change (if p 161 then d2 (change p 133 (some 134)) else d1 (change p 133 (some 134))) = d9 p
  rw [sub1631, sub1638]
  rfl
theorem sub1640 (p : Pattern) : d10 (change p 133 (some 134)) = d10 p := by
  change (if p 160 then d9 (change p 133 (some 134)) else d1 (change p 133 (some 134))) = d10 p
  rw [sub1639, sub1638]
  rfl
theorem sub1641 (p : Pattern) : d11 (change p 133 (some 134)) = d11 p := by
  change (if p 160 then d2 (change p 133 (some 134)) else d1 (change p 133 (some 134))) = d11 p
  rw [sub1631, sub1638]
  rfl
theorem sub1642 (p : Pattern) : d12 (change p 133 (some 134)) = d12 p := by
  change (if p 159 then d11 (change p 133 (some 134)) else d10 (change p 133 (some 134))) = d12 p
  rw [sub1641, sub1640]
  rfl
theorem sub1643 (p : Pattern) : d13 (change p 133 (some 134)) = d13 p := by
  change (if p 159 then d2 (change p 133 (some 134)) else d10 (change p 133 (some 134))) = d13 p
  rw [sub1631, sub1640]
  rfl
theorem sub1644 (p : Pattern) : d14 (change p 133 (some 134)) = d14 p := by
  change (if p 158 then d13 (change p 133 (some 134)) else d12 (change p 133 (some 134))) = d14 p
  rw [sub1643, sub1642]
  rfl
theorem sub1645 (p : Pattern) : d15 (change p 133 (some 134)) = d15 p := by
  change (if p 139 then d14 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d15 p
  rw [sub1644, sub1637]
  rfl
theorem sub1646 (p : Pattern) : d16 (change p 133 (some 134)) = d16 p := by
  change (if p 138 then d15 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d16 p
  rw [sub1645, sub1637]
  rfl
theorem sub1647 (p : Pattern) : d293 (change p 133 (some 134)) = d16 p := by
  change d16 (change p 133 (some 134)) = d16 p
  exact sub1646 p
theorem sub1648 (p : Pattern) : d294 (change p 133 (some 134)) = d15 p := by
  change d15 (change p 133 (some 134)) = d15 p
  exact sub1645 p
theorem sub1649 (p : Pattern) : d52 (change p 133 (some 134)) = d52 p := by
  change (if p 139 then d2 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d52 p
  rw [sub1631, sub1637]
  rfl
theorem sub1650 (p : Pattern) : d53 (change p 133 (some 134)) = d53 p := by
  change (if p 138 then d52 (change p 133 (some 134)) else d15 (change p 133 (some 134))) = d53 p
  rw [sub1649, sub1645]
  rfl
theorem sub1651 (p : Pattern) : d295 (change p 133 (some 134)) = d53 p := by
  change d53 (change p 133 (some 134)) = d53 p
  exact sub1650 p
theorem sub1652 (p : Pattern) : d296 (change p 133 (some 134)) = d1152 p := by
  change (if p 113 then d295 (change p 133 (some 134)) else d294 (change p 133 (some 134))) = d1152 p
  rw [sub1651, sub1648]
  rfl
theorem sub1653 (p : Pattern) : d297 (change p 133 (some 134)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 134)) else d293 (change p 133 (some 134))) = d1153 p
  rw [sub1652, sub1647]
  rfl
theorem sub1654 (p : Pattern) : d298 (change p 133 (some 134)) = d16 p := by
  change d16 (change p 133 (some 134)) = d16 p
  exact sub1646 p
theorem sub1655 (p : Pattern) : d299 (change p 133 (some 134)) = d16 p := by
  change (if p 132 then d298 (change p 133 (some 134)) else d293 (change p 133 (some 134))) = d16 p
  rw [sub1654, sub1647]
  simp only [ite_self]
theorem sub1656 (p : Pattern) : d300 (change p 133 (some 134)) = d16 p := by
  change (if p 113 then d299 (change p 133 (some 134)) else d293 (change p 133 (some 134))) = d16 p
  rw [sub1655, sub1647]
  simp only [ite_self]
theorem sub1657 (p : Pattern) : d301 (change p 133 (some 134)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 134)) else d300 (change p 133 (some 134))) = d1153 p
  rw [sub1652, sub1656]
  rfl
theorem sub1658 (p : Pattern) : d302 (change p 133 (some 134)) = d1153 p := by
  change (if p 106 then d301 (change p 133 (some 134)) else d297 (change p 133 (some 134))) = d1153 p
  rw [sub1657, sub1653]
  simp only [ite_self]
theorem sub1659 (p : Pattern) : d86 (change p 133 (some 134)) = d86 p := by
  change (if p 138 then d52 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d86 p
  rw [sub1649, sub1637]
  rfl
theorem sub1660 (p : Pattern) : d303 (change p 133 (some 134)) = d86 p := by
  change d86 (change p 133 (some 134)) = d86 p
  exact sub1659 p
theorem sub1661 (p : Pattern) : d304 (change p 133 (some 134)) = d86 p := by
  change d86 (change p 133 (some 134)) = d86 p
  exact sub1659 p
theorem sub1662 (p : Pattern) : d305 (change p 133 (some 134)) = d86 p := by
  change (if p 132 then d304 (change p 133 (some 134)) else d303 (change p 133 (some 134))) = d86 p
  rw [sub1661, sub1660]
  simp only [ite_self]
theorem sub1663 (p : Pattern) : d306 (change p 133 (some 134)) = d1154 p := by
  change (if p 113 then d305 (change p 133 (some 134)) else d293 (change p 133 (some 134))) = d1154 p
  rw [sub1662, sub1647]
  rfl
theorem sub1664 (p : Pattern) : d97 (change p 133 (some 134)) = d97 p := by
  change (if p 139 then d2 (change p 133 (some 134)) else d14 (change p 133 (some 134))) = d97 p
  rw [sub1631, sub1644]
  rfl
theorem sub1665 (p : Pattern) : d98 (change p 133 (some 134)) = d98 p := by
  change (if p 138 then d97 (change p 133 (some 134)) else d14 (change p 133 (some 134))) = d98 p
  rw [sub1664, sub1644]
  rfl
theorem sub1666 (p : Pattern) : d307 (change p 133 (some 134)) = d98 p := by
  change d98 (change p 133 (some 134)) = d98 p
  exact sub1665 p
theorem sub1667 (p : Pattern) : d308 (change p 133 (some 134)) = d1155 p := by
  change (if p 112 then d307 (change p 133 (some 134)) else d306 (change p 133 (some 134))) = d1155 p
  rw [sub1666, sub1663]
  rfl
theorem sub1668 (p : Pattern) : d309 (change p 133 (some 134)) = d86 p := by
  change d86 (change p 133 (some 134)) = d86 p
  exact sub1659 p
theorem sub1669 (p : Pattern) : d310 (change p 133 (some 134)) = d86 p := by
  change (if p 132 then d309 (change p 133 (some 134)) else d304 (change p 133 (some 134))) = d86 p
  rw [sub1668, sub1661]
  simp only [ite_self]
theorem sub1670 (p : Pattern) : d311 (change p 133 (some 134)) = d1154 p := by
  change (if p 113 then d310 (change p 133 (some 134)) else d299 (change p 133 (some 134))) = d1154 p
  rw [sub1669, sub1655]
  rfl
theorem sub1671 (p : Pattern) : d312 (change p 133 (some 134)) = d97 p := by
  change d97 (change p 133 (some 134)) = d97 p
  exact sub1664 p
theorem sub1672 (p : Pattern) : d313 (change p 133 (some 134)) = d1156 p := by
  change (if p 113 then d312 (change p 133 (some 134)) else d307 (change p 133 (some 134))) = d1156 p
  rw [sub1671, sub1666]
  rfl
theorem sub1673 (p : Pattern) : d314 (change p 133 (some 134)) = d1157 p := by
  change (if p 112 then d313 (change p 133 (some 134)) else d311 (change p 133 (some 134))) = d1157 p
  rw [sub1672, sub1670]
  rfl
theorem sub1674 (p : Pattern) : d315 (change p 133 (some 134)) = d1158 p := by
  change (if p 106 then d314 (change p 133 (some 134)) else d308 (change p 133 (some 134))) = d1158 p
  rw [sub1673, sub1667]
  rfl
theorem sub1675 (p : Pattern) : d316 (change p 133 (some 134)) = d1159 p := by
  change (if p 86 then d315 (change p 133 (some 134)) else d302 (change p 133 (some 134))) = d1159 p
  rw [sub1674, sub1658]
  rfl
theorem sub1676 (p : Pattern) : d317 (change p 133 (some 134)) = d16 p := by
  change d16 (change p 133 (some 134)) = d16 p
  exact sub1646 p
theorem sub1677 (p : Pattern) : d318 (change p 133 (some 134)) = d16 p := by
  change (if p 132 then d317 (change p 133 (some 134)) else d298 (change p 133 (some 134))) = d16 p
  rw [sub1676, sub1654]
  simp only [ite_self]
theorem sub1678 (p : Pattern) : d319 (change p 133 (some 134)) = d16 p := by
  change (if p 113 then d318 (change p 133 (some 134)) else d299 (change p 133 (some 134))) = d16 p
  rw [sub1677, sub1655]
  simp only [ite_self]
theorem sub1679 (p : Pattern) : d320 (change p 133 (some 134)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 134)) else d319 (change p 133 (some 134))) = d1153 p
  rw [sub1652, sub1678]
  rfl
end NetHack.Sokoban32Refined
