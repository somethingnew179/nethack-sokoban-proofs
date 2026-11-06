/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1560 (p : Pattern) : d37 (change p 10000 (some 71)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 71)) else d14 (change p 10000 (some 71))) = d37 p
  rw [sub1559, sub1533]
  rfl
theorem sub1561 (p : Pattern) : d38 (change p 10000 (some 71)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 71)) else d33 (change p 10000 (some 71))) = d38 p
  rw [sub1560, sub1555]
  rfl
theorem sub1562 (p : Pattern) : d11 (change p 10000 (some 71)) = d11 p := by
  rfl
theorem sub1563 (p : Pattern) : d39 (change p 10000 (some 71)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d11 (change p 10000 (some 71))) = d39 p
  rw [sub1531, sub1562]
  rfl
theorem sub1564 (p : Pattern) : d40 (change p 10000 (some 71)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 71)) else d11 (change p 10000 (some 71))) = d40 p
  rw [sub1563, sub1562]
  rfl
theorem sub1565 (p : Pattern) : d41 (change p 10000 (some 71)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d40 (change p 10000 (some 71))) = d41 p
  rw [sub1531, sub1564]
  rfl
theorem sub1566 (p : Pattern) : d42 (change p 10000 (some 71)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 71)) else d14 (change p 10000 (some 71))) = d42 p
  rw [sub1565, sub1533]
  rfl
theorem sub1567 (p : Pattern) : d43 (change p 10000 (some 71)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d18 (change p 10000 (some 71))) = d43 p
  rw [sub1531, sub1538]
  rfl
theorem sub1568 (p : Pattern) : d44 (change p 10000 (some 71)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 71)) else d42 (change p 10000 (some 71))) = d44 p
  rw [sub1567, sub1566]
  rfl
theorem sub1569 (p : Pattern) : d45 (change p 10000 (some 71)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 71)) else d38 (change p 10000 (some 71))) = d45 p
  rw [sub1568, sub1561]
  rfl
theorem sub1570 (p : Pattern) : d46 (change p 10000 (some 71)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d14 (change p 10000 (some 71))) = d46 p
  rw [sub1531, sub1533]
  rfl
theorem sub1571 (p : Pattern) : d47 (change p 10000 (some 71)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 71)) else d46 (change p 10000 (some 71))) = d47 p
  rw [sub1567, sub1570]
  rfl
theorem sub1572 (p : Pattern) : d48 (change p 10000 (some 71)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d24 (change p 10000 (some 71))) = d48 p
  rw [sub1531, sub1545]
  rfl
theorem sub1573 (p : Pattern) : d49 (change p 10000 (some 71)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d48 (change p 10000 (some 71))) = d49 p
  rw [sub1531, sub1572]
  rfl
theorem sub1574 (p : Pattern) : d50 (change p 10000 (some 71)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 71)) else d47 (change p 10000 (some 71))) = d50 p
  rw [sub1573, sub1571]
  rfl
theorem sub1575 (p : Pattern) : d51 (change p 10000 (some 71)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 71)) else d45 (change p 10000 (some 71))) = d51 p
  rw [sub1574, sub1569]
  rfl
theorem sub1576 (p : Pattern) : d52 (change p 10000 (some 71)) = d52 p := by
  change (if p 160 then d51 (change p 10000 (some 71)) else d29 (change p 10000 (some 71))) = d52 p
  rw [sub1575, sub1550]
  rfl
theorem sub1577 (p : Pattern) : d53 (change p 10000 (some 71)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 71)) else d31 (change p 10000 (some 71))) = d53 p
  rw [sub1554, sub1553]
  rfl
theorem sub1578 (p : Pattern) : d54 (change p 10000 (some 71)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 71)) else d16 (change p 10000 (some 71))) = d54 p
  rw [sub1577, sub1535]
  rfl
theorem sub1579 (p : Pattern) : d55 (change p 10000 (some 71)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 71)) else d20 (change p 10000 (some 71))) = d55 p
  rw [sub1547, sub1540]
  rfl
theorem sub1580 (p : Pattern) : d56 (change p 10000 (some 71)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 71)) else d54 (change p 10000 (some 71))) = d56 p
  rw [sub1579, sub1578]
  rfl
theorem sub1581 (p : Pattern) : d10 (change p 10000 (some 71)) = d10 p := by
  rfl
theorem sub1582 (p : Pattern) : d57 (change p 10000 (some 71)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d10 (change p 10000 (some 71))) = d57 p
  rw [sub1531, sub1581]
  rfl
theorem sub1583 (p : Pattern) : d58 (change p 10000 (some 71)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 71)) else d10 (change p 10000 (some 71))) = d58 p
  rw [sub1582, sub1581]
  rfl
theorem sub1584 (p : Pattern) : d59 (change p 10000 (some 71)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d58 (change p 10000 (some 71))) = d59 p
  rw [sub1531, sub1583]
  rfl
theorem sub1585 (p : Pattern) : d60 (change p 10000 (some 71)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 71)) else d58 (change p 10000 (some 71))) = d60 p
  rw [sub1584, sub1583]
  rfl
theorem sub1586 (p : Pattern) : d61 (change p 10000 (some 71)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 71)) else d20 (change p 10000 (some 71))) = d61 p
  rw [sub1585, sub1540]
  rfl
theorem sub1587 (p : Pattern) : d62 (change p 10000 (some 71)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 71)) else d40 (change p 10000 (some 71))) = d62 p
  rw [sub1565, sub1564]
  rfl
theorem sub1588 (p : Pattern) : d63 (change p 10000 (some 71)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d62 (change p 10000 (some 71))) = d63 p
  rw [sub1531, sub1587]
  rfl
theorem sub1589 (p : Pattern) : d64 (change p 10000 (some 71)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 71)) else d61 (change p 10000 (some 71))) = d64 p
  rw [sub1588, sub1586]
  rfl
theorem sub1590 (p : Pattern) : d65 (change p 10000 (some 71)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 71)) else d56 (change p 10000 (some 71))) = d65 p
  rw [sub1589, sub1580]
  rfl
theorem sub1591 (p : Pattern) : d66 (change p 10000 (some 71)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d31 (change p 10000 (some 71))) = d66 p
  rw [sub1531, sub1553]
  rfl
theorem sub1592 (p : Pattern) : d67 (change p 10000 (some 71)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 71)) else d37 (change p 10000 (some 71))) = d67 p
  rw [sub1591, sub1560]
  rfl
theorem sub1593 (p : Pattern) : d68 (change p 10000 (some 71)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 71)) else d43 (change p 10000 (some 71))) = d68 p
  rw [sub1572, sub1567]
  rfl
theorem sub1594 (p : Pattern) : d69 (change p 10000 (some 71)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 71)) else d67 (change p 10000 (some 71))) = d69 p
  rw [sub1593, sub1592]
  rfl
theorem sub1595 (p : Pattern) : d70 (change p 10000 (some 71)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d58 (change p 10000 (some 71))) = d70 p
  rw [sub1531, sub1583]
  rfl
theorem sub1596 (p : Pattern) : d71 (change p 10000 (some 71)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 71)) else d43 (change p 10000 (some 71))) = d71 p
  rw [sub1595, sub1567]
  rfl
theorem sub1597 (p : Pattern) : d72 (change p 10000 (some 71)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d40 (change p 10000 (some 71))) = d72 p
  rw [sub1531, sub1564]
  rfl
theorem sub1598 (p : Pattern) : d73 (change p 10000 (some 71)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d72 (change p 10000 (some 71))) = d73 p
  rw [sub1531, sub1597]
  rfl
theorem sub1599 (p : Pattern) : d74 (change p 10000 (some 71)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 71)) else d71 (change p 10000 (some 71))) = d74 p
  rw [sub1598, sub1596]
  rfl
theorem sub1600 (p : Pattern) : d75 (change p 10000 (some 71)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 71)) else d69 (change p 10000 (some 71))) = d75 p
  rw [sub1599, sub1594]
  rfl
theorem sub1601 (p : Pattern) : d76 (change p 10000 (some 71)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 71)) else d65 (change p 10000 (some 71))) = d76 p
  rw [sub1600, sub1590]
  rfl
theorem sub1602 (p : Pattern) : d77 (change p 10000 (some 71)) = d77 p := by
  change (if p 141 then d76 (change p 10000 (some 71)) else d52 (change p 10000 (some 71))) = d77 p
  rw [sub1601, sub1576]
  rfl
theorem sub1603 (p : Pattern) : d78 (change p 10000 (some 71)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 71)) else d35 (change p 10000 (some 71))) = d78 p
  rw [sub1559, sub1558]
  rfl
theorem sub1604 (p : Pattern) : d79 (change p 10000 (some 71)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 71)) else d53 (change p 10000 (some 71))) = d79 p
  rw [sub1603, sub1577]
  rfl
theorem sub1605 (p : Pattern) : d80 (change p 10000 (some 71)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 71)) else d79 (change p 10000 (some 71))) = d80 p
  rw [sub1588, sub1604]
  rfl
theorem sub1606 (p : Pattern) : d81 (change p 10000 (some 71)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d80 (change p 10000 (some 71))) = d81 p
  rw [sub1531, sub1605]
  rfl
theorem sub1607 (p : Pattern) : d82 (change p 10000 (some 71)) = d82 p := by
  change (if p 160 then d81 (change p 10000 (some 71)) else d29 (change p 10000 (some 71))) = d82 p
  rw [sub1606, sub1550]
  rfl
theorem sub1608 (p : Pattern) : d83 (change p 10000 (some 71)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d78 (change p 10000 (some 71))) = d83 p
  rw [sub1531, sub1603]
  rfl
theorem sub1609 (p : Pattern) : d84 (change p 10000 (some 71)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d83 (change p 10000 (some 71))) = d84 p
  rw [sub1531, sub1608]
  rfl
theorem sub1610 (p : Pattern) : d85 (change p 10000 (some 71)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d84 (change p 10000 (some 71))) = d85 p
  rw [sub1531, sub1609]
  rfl
theorem sub1611 (p : Pattern) : d86 (change p 10000 (some 71)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 71)) else d65 (change p 10000 (some 71))) = d86 p
  rw [sub1610, sub1590]
  rfl
theorem sub1612 (p : Pattern) : d87 (change p 10000 (some 71)) = d87 p := by
  change (if p 141 then d86 (change p 10000 (some 71)) else d82 (change p 10000 (some 71))) = d87 p
  rw [sub1611, sub1607]
  rfl
theorem sub1613 (p : Pattern) : d88 (change p 10000 (some 71)) = d88 p := by
  change (if p 138 then d87 (change p 10000 (some 71)) else d77 (change p 10000 (some 71))) = d88 p
  rw [sub1612, sub1602]
  rfl
theorem sub1614 (p : Pattern) : d89 (change p 10000 (some 71)) = d89 p := by
  change (if p 163 then d62 (change p 10000 (some 71)) else d26 (change p 10000 (some 71))) = d89 p
  rw [sub1587, sub1547]
  rfl
theorem sub1615 (p : Pattern) : d90 (change p 10000 (some 71)) = d90 p := by
  change (if p 162 then d63 (change p 10000 (some 71)) else d89 (change p 10000 (some 71))) = d90 p
  rw [sub1588, sub1614]
  rfl
theorem sub1616 (p : Pattern) : d91 (change p 10000 (some 71)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d63 (change p 10000 (some 71))) = d91 p
  rw [sub1531, sub1588]
  rfl
theorem sub1617 (p : Pattern) : d92 (change p 10000 (some 71)) = d92 p := by
  change (if p 161 then d91 (change p 10000 (some 71)) else d90 (change p 10000 (some 71))) = d92 p
  rw [sub1616, sub1615]
  rfl
theorem sub1618 (p : Pattern) : d93 (change p 10000 (some 71)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d91 (change p 10000 (some 71))) = d93 p
  rw [sub1531, sub1616]
  rfl
theorem sub1619 (p : Pattern) : d94 (change p 10000 (some 71)) = d94 p := by
  change (if p 160 then d93 (change p 10000 (some 71)) else d92 (change p 10000 (some 71))) = d94 p
  rw [sub1618, sub1617]
  rfl
theorem sub1620 (p : Pattern) : d95 (change p 10000 (some 71)) = d95 p := by
  change (if p 160 then d12 (change p 10000 (some 71)) else d93 (change p 10000 (some 71))) = d95 p
  rw [sub1531, sub1618]
  rfl
theorem sub1621 (p : Pattern) : d96 (change p 10000 (some 71)) = d96 p := by
  change (if p 141 then d95 (change p 10000 (some 71)) else d94 (change p 10000 (some 71))) = d96 p
  rw [sub1620, sub1619]
  rfl
theorem sub1622 (p : Pattern) : d97 (change p 10000 (some 71)) = d97 p := by
  change (if p 138 then d96 (change p 10000 (some 71)) else d87 (change p 10000 (some 71))) = d97 p
  rw [sub1621, sub1612]
  rfl
theorem sub1623 (p : Pattern) : d98 (change p 10000 (some 71)) = d98 p := by
  change (if p 116 then d97 (change p 10000 (some 71)) else d88 (change p 10000 (some 71))) = d98 p
  rw [sub1622, sub1613]
  rfl
theorem sub1624 (p : Pattern) : d99 (change p 10000 (some 71)) = d99 p := by
  change (if p 138 then d12 (change p 10000 (some 71)) else d87 (change p 10000 (some 71))) = d99 p
  rw [sub1531, sub1612]
  rfl
theorem sub1625 (p : Pattern) : d100 (change p 10000 (some 71)) = d100 p := by
  change (if p 116 then d99 (change p 10000 (some 71)) else d88 (change p 10000 (some 71))) = d100 p
  rw [sub1624, sub1613]
  rfl
theorem sub1626 (p : Pattern) : d101 (change p 10000 (some 71)) = d101 p := by
  change (if p 115 then d100 (change p 10000 (some 71)) else d98 (change p 10000 (some 71))) = d101 p
  rw [sub1625, sub1623]
  rfl
theorem sub1627 (p : Pattern) : d1 (change p 10000 (some 71)) = d1 p := by
  rfl
theorem sub1628 (p : Pattern) : d102 (change p 10000 (some 71)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d1 (change p 10000 (some 71))) = d102 p
  rw [sub1531, sub1627]
  rfl
theorem sub1629 (p : Pattern) : d103 (change p 10000 (some 71)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 71)) else d1 (change p 10000 (some 71))) = d103 p
  rw [sub1628, sub1627]
  rfl
theorem sub1630 (p : Pattern) : d104 (change p 10000 (some 71)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d104 p
  rw [sub1531, sub1629]
  rfl
theorem sub1631 (p : Pattern) : d105 (change p 10000 (some 71)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d105 p
  rw [sub1630, sub1629]
  rfl
theorem sub1632 (p : Pattern) : d5 (change p 10000 (some 71)) = d5 p := by
  rfl
theorem sub1633 (p : Pattern) : d106 (change p 10000 (some 71)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d5 (change p 10000 (some 71))) = d106 p
  rw [sub1531, sub1632]
  rfl
theorem sub1634 (p : Pattern) : d107 (change p 10000 (some 71)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 71)) else d5 (change p 10000 (some 71))) = d107 p
  rw [sub1633, sub1632]
  rfl
theorem sub1635 (p : Pattern) : d108 (change p 10000 (some 71)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d107 (change p 10000 (some 71))) = d108 p
  rw [sub1531, sub1634]
  rfl
theorem sub1636 (p : Pattern) : d109 (change p 10000 (some 71)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 71)) else d107 (change p 10000 (some 71))) = d109 p
  rw [sub1635, sub1634]
  rfl
theorem sub1637 (p : Pattern) : d110 (change p 10000 (some 71)) = d110 p := by
  change (if p 163 then d109 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d110 p
  rw [sub1636, sub1631]
  rfl
theorem sub1638 (p : Pattern) : d111 (change p 10000 (some 71)) = d111 p := by
  change (if p 162 then d110 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d111 p
  rw [sub1637, sub1631]
  rfl
theorem sub1639 (p : Pattern) : d112 (change p 10000 (some 71)) = d112 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d60 (change p 10000 (some 71))) = d112 p
  rw [sub1531, sub1585]
  rfl
theorem sub1640 (p : Pattern) : d113 (change p 10000 (some 71)) = d113 p := by
  change (if p 162 then d112 (change p 10000 (some 71)) else d110 (change p 10000 (some 71))) = d113 p
  rw [sub1639, sub1637]
  rfl
theorem sub1641 (p : Pattern) : d114 (change p 10000 (some 71)) = d114 p := by
  change (if p 161 then d113 (change p 10000 (some 71)) else d111 (change p 10000 (some 71))) = d114 p
  rw [sub1640, sub1638]
  rfl
theorem sub1642 (p : Pattern) : d3 (change p 10000 (some 71)) = d3 p := by
  rfl
theorem sub1643 (p : Pattern) : d115 (change p 10000 (some 71)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d3 (change p 10000 (some 71))) = d115 p
  rw [sub1531, sub1642]
  rfl
theorem sub1644 (p : Pattern) : d116 (change p 10000 (some 71)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 71)) else d3 (change p 10000 (some 71))) = d116 p
  rw [sub1643, sub1642]
  rfl
theorem sub1645 (p : Pattern) : d117 (change p 10000 (some 71)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d116 (change p 10000 (some 71))) = d117 p
  rw [sub1531, sub1644]
  rfl
theorem sub1646 (p : Pattern) : d118 (change p 10000 (some 71)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d118 p
  rw [sub1645, sub1629]
  rfl
theorem sub1647 (p : Pattern) : d7 (change p 10000 (some 71)) = d7 p := by
  rfl
theorem sub1648 (p : Pattern) : d119 (change p 10000 (some 71)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d7 (change p 10000 (some 71))) = d119 p
  rw [sub1531, sub1647]
  rfl
theorem sub1649 (p : Pattern) : d120 (change p 10000 (some 71)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 71)) else d7 (change p 10000 (some 71))) = d120 p
  rw [sub1648, sub1647]
  rfl
theorem sub1650 (p : Pattern) : d121 (change p 10000 (some 71)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d120 (change p 10000 (some 71))) = d121 p
  rw [sub1531, sub1649]
  rfl
theorem sub1651 (p : Pattern) : d122 (change p 10000 (some 71)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d122 p
  rw [sub1650, sub1629]
  rfl
theorem sub1652 (p : Pattern) : d123 (change p 10000 (some 71)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 71)) else d118 (change p 10000 (some 71))) = d123 p
  rw [sub1651, sub1646]
  rfl
theorem sub1653 (p : Pattern) : d124 (change p 10000 (some 71)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d124 p
  rw [sub1531, sub1629]
  rfl
theorem sub1654 (p : Pattern) : d125 (change p 10000 (some 71)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d107 (change p 10000 (some 71))) = d125 p
  rw [sub1531, sub1634]
  rfl
theorem sub1655 (p : Pattern) : d126 (change p 10000 (some 71)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 71)) else d124 (change p 10000 (some 71))) = d126 p
  rw [sub1654, sub1653]
  rfl
theorem sub1656 (p : Pattern) : d127 (change p 10000 (some 71)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 71)) else d123 (change p 10000 (some 71))) = d127 p
  rw [sub1655, sub1652]
  rfl
theorem sub1657 (p : Pattern) : d128 (change p 10000 (some 71)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d70 (change p 10000 (some 71))) = d128 p
  rw [sub1531, sub1595]
  rfl
theorem sub1658 (p : Pattern) : d129 (change p 10000 (some 71)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 71)) else d126 (change p 10000 (some 71))) = d129 p
  rw [sub1657, sub1655]
  rfl
theorem sub1659 (p : Pattern) : d130 (change p 10000 (some 71)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 71)) else d127 (change p 10000 (some 71))) = d130 p
  rw [sub1658, sub1656]
  rfl
theorem sub1660 (p : Pattern) : d131 (change p 10000 (some 71)) = d131 p := by
  change (if p 160 then d130 (change p 10000 (some 71)) else d114 (change p 10000 (some 71))) = d131 p
  rw [sub1659, sub1641]
  rfl
theorem sub1661 (p : Pattern) : d132 (change p 10000 (some 71)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 71)) else d116 (change p 10000 (some 71))) = d132 p
  rw [sub1645, sub1644]
  rfl
theorem sub1662 (p : Pattern) : d133 (change p 10000 (some 71)) = d133 p := by
  change (if p 163 then d132 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d133 p
  rw [sub1661, sub1631]
  rfl
theorem sub1663 (p : Pattern) : d134 (change p 10000 (some 71)) = d134 p := by
  change (if p 163 then d60 (change p 10000 (some 71)) else d109 (change p 10000 (some 71))) = d134 p
  rw [sub1585, sub1636]
  rfl
theorem sub1664 (p : Pattern) : d135 (change p 10000 (some 71)) = d135 p := by
  change (if p 162 then d134 (change p 10000 (some 71)) else d133 (change p 10000 (some 71))) = d135 p
  rw [sub1663, sub1662]
  rfl
theorem sub1665 (p : Pattern) : d136 (change p 10000 (some 71)) = d136 p := by
  change (if p 163 then d62 (change p 10000 (some 71)) else d109 (change p 10000 (some 71))) = d136 p
  rw [sub1587, sub1636]
  rfl
theorem sub1666 (p : Pattern) : d137 (change p 10000 (some 71)) = d137 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d136 (change p 10000 (some 71))) = d137 p
  rw [sub1531, sub1665]
  rfl
theorem sub1667 (p : Pattern) : d138 (change p 10000 (some 71)) = d138 p := by
  change (if p 161 then d137 (change p 10000 (some 71)) else d135 (change p 10000 (some 71))) = d138 p
  rw [sub1666, sub1664]
  rfl
theorem sub1668 (p : Pattern) : d139 (change p 10000 (some 71)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d116 (change p 10000 (some 71))) = d139 p
  rw [sub1531, sub1644]
  rfl
theorem sub1669 (p : Pattern) : d140 (change p 10000 (some 71)) = d140 p := by
  change (if p 163 then d139 (change p 10000 (some 71)) else d122 (change p 10000 (some 71))) = d140 p
  rw [sub1668, sub1651]
  rfl
theorem sub1670 (p : Pattern) : d141 (change p 10000 (some 71)) = d141 p := by
  change (if p 163 then d70 (change p 10000 (some 71)) else d125 (change p 10000 (some 71))) = d141 p
  rw [sub1595, sub1654]
  rfl
theorem sub1671 (p : Pattern) : d142 (change p 10000 (some 71)) = d142 p := by
  change (if p 162 then d141 (change p 10000 (some 71)) else d140 (change p 10000 (some 71))) = d142 p
  rw [sub1670, sub1669]
  rfl
theorem sub1672 (p : Pattern) : d143 (change p 10000 (some 71)) = d143 p := by
  change (if p 163 then d72 (change p 10000 (some 71)) else d125 (change p 10000 (some 71))) = d143 p
  rw [sub1597, sub1654]
  rfl
theorem sub1673 (p : Pattern) : d144 (change p 10000 (some 71)) = d144 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d143 (change p 10000 (some 71))) = d144 p
  rw [sub1531, sub1672]
  rfl
theorem sub1674 (p : Pattern) : d145 (change p 10000 (some 71)) = d145 p := by
  change (if p 161 then d144 (change p 10000 (some 71)) else d142 (change p 10000 (some 71))) = d145 p
  rw [sub1673, sub1671]
  rfl
theorem sub1675 (p : Pattern) : d146 (change p 10000 (some 71)) = d146 p := by
  change (if p 160 then d145 (change p 10000 (some 71)) else d138 (change p 10000 (some 71))) = d146 p
  rw [sub1674, sub1667]
  rfl
theorem sub1676 (p : Pattern) : d147 (change p 10000 (some 71)) = d147 p := by
  change (if p 141 then d146 (change p 10000 (some 71)) else d131 (change p 10000 (some 71))) = d147 p
  rw [sub1675, sub1660]
  rfl
theorem sub1677 (p : Pattern) : d148 (change p 10000 (some 71)) = d148 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d120 (change p 10000 (some 71))) = d148 p
  rw [sub1650, sub1649]
  rfl
theorem sub1678 (p : Pattern) : d149 (change p 10000 (some 71)) = d149 p := by
  change (if p 163 then d148 (change p 10000 (some 71)) else d132 (change p 10000 (some 71))) = d149 p
  rw [sub1677, sub1661]
  rfl
theorem sub1679 (p : Pattern) : d150 (change p 10000 (some 71)) = d150 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d149 (change p 10000 (some 71))) = d150 p
  rw [sub1531, sub1678]
  rfl
end NetHack.Sokoban22Refined85
