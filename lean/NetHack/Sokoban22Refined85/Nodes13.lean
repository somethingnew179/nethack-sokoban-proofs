/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1560 (p : Pattern) : Int := if p 161 then d74 p else d1559 p
theorem agree1560 (p q : Pattern) (h : Agree support p q) : d1560 p = d1560 q := by
  simp only [d1560, h 161 (by decide), agree74 p q h, agree1559 p q h]
theorem nonnegative1560 (p : Pattern) : 0 ≤ d1560 p :=
  nonnegative_ite (p 161) (nonnegative74 p) (nonnegative1559 p)
def d1561 (p : Pattern) : Int := if p 160 then d1520 p else d1560 p
theorem agree1561 (p q : Pattern) (h : Agree support p q) : d1561 p = d1561 q := by
  simp only [d1561, h 160 (by decide), agree1520 p q h, agree1560 p q h]
theorem nonnegative1561 (p : Pattern) : 0 ≤ d1561 p :=
  nonnegative_ite (p 160) (nonnegative1520 p) (nonnegative1560 p)
def d1562 (p : Pattern) : Int := if p 141 then d1561 p else d1557 p
theorem agree1562 (p q : Pattern) (h : Agree support p q) : d1562 p = d1562 q := by
  simp only [d1562, h 141 (by decide), agree1561 p q h, agree1557 p q h]
theorem nonnegative1562 (p : Pattern) : 0 ≤ d1562 p :=
  nonnegative_ite (p 141) (nonnegative1561 p) (nonnegative1557 p)
def d1563 (p : Pattern) : Int := if p 138 then d1527 p else d1562 p
theorem agree1563 (p q : Pattern) (h : Agree support p q) : d1563 p = d1563 q := by
  simp only [d1563, h 138 (by decide), agree1527 p q h, agree1562 p q h]
theorem nonnegative1563 (p : Pattern) : 0 ≤ d1563 p :=
  nonnegative_ite (p 138) (nonnegative1527 p) (nonnegative1562 p)
def d1564 (p : Pattern) : Int := if p 138 then d1541 p else d1527 p
theorem agree1564 (p q : Pattern) (h : Agree support p q) : d1564 p = d1564 q := by
  simp only [d1564, h 138 (by decide), agree1541 p q h, agree1527 p q h]
theorem nonnegative1564 (p : Pattern) : 0 ≤ d1564 p :=
  nonnegative_ite (p 138) (nonnegative1541 p) (nonnegative1527 p)
def d1565 (p : Pattern) : Int := if p 116 then d1564 p else d1563 p
theorem agree1565 (p q : Pattern) (h : Agree support p q) : d1565 p = d1565 q := by
  simp only [d1565, h 116 (by decide), agree1564 p q h, agree1563 p q h]
theorem nonnegative1565 (p : Pattern) : 0 ≤ d1565 p :=
  nonnegative_ite (p 116) (nonnegative1564 p) (nonnegative1563 p)
def d1566 (p : Pattern) : Int := if p 160 then d1512 p else d1531 p
theorem agree1566 (p q : Pattern) (h : Agree support p q) : d1566 p = d1566 q := by
  simp only [d1566, h 160 (by decide), agree1512 p q h, agree1531 p q h]
theorem nonnegative1566 (p : Pattern) : 0 ≤ d1566 p :=
  nonnegative_ite (p 160) (nonnegative1512 p) (nonnegative1531 p)
def d1567 (p : Pattern) : Int := if p 141 then d1520 p else d1566 p
theorem agree1567 (p q : Pattern) (h : Agree support p q) : d1567 p = d1567 q := by
  simp only [d1567, h 141 (by decide), agree1520 p q h, agree1566 p q h]
theorem nonnegative1567 (p : Pattern) : 0 ≤ d1567 p :=
  nonnegative_ite (p 141) (nonnegative1520 p) (nonnegative1566 p)
def d1568 (p : Pattern) : Int := if p 138 then d1527 p else d1567 p
theorem agree1568 (p q : Pattern) (h : Agree support p q) : d1568 p = d1568 q := by
  simp only [d1568, h 138 (by decide), agree1527 p q h, agree1567 p q h]
theorem nonnegative1568 (p : Pattern) : 0 ≤ d1568 p :=
  nonnegative_ite (p 138) (nonnegative1527 p) (nonnegative1567 p)
def d1569 (p : Pattern) : Int := if p 116 then d1550 p else d1568 p
theorem agree1569 (p q : Pattern) (h : Agree support p q) : d1569 p = d1569 q := by
  simp only [d1569, h 116 (by decide), agree1550 p q h, agree1568 p q h]
theorem nonnegative1569 (p : Pattern) : 0 ≤ d1569 p :=
  nonnegative_ite (p 116) (nonnegative1550 p) (nonnegative1568 p)
def d1570 (p : Pattern) : Int := if p 115 then d1569 p else d1565 p
theorem agree1570 (p q : Pattern) (h : Agree support p q) : d1570 p = d1570 q := by
  simp only [d1570, h 115 (by decide), agree1569 p q h, agree1565 p q h]
theorem nonnegative1570 (p : Pattern) : 0 ≤ d1570 p :=
  nonnegative_ite (p 115) (nonnegative1569 p) (nonnegative1565 p)
def d1571 (p : Pattern) : Int := if p 71 then d1570 p else d1552 p
theorem agree1571 (p q : Pattern) (h : Agree support p q) : d1571 p = d1571 q := by
  simp only [d1571, h 71 (by decide), agree1570 p q h, agree1552 p q h]
theorem nonnegative1571 (p : Pattern) : 0 ≤ d1571 p :=
  nonnegative_ite (p 71) (nonnegative1570 p) (nonnegative1552 p)
def d1572 (p : Pattern) : Int := if p 182 then d353 p else d103 p
theorem agree1572 (p q : Pattern) (h : Agree support p q) : d1572 p = d1572 q := by
  simp only [d1572, h 182 (by decide), agree353 p q h, agree103 p q h]
theorem nonnegative1572 (p : Pattern) : 0 ≤ d1572 p :=
  nonnegative_ite (p 182) (nonnegative353 p) (nonnegative103 p)
def d1573 (p : Pattern) : Int := if p 182 then d343 p else d103 p
theorem agree1573 (p q : Pattern) (h : Agree support p q) : d1573 p = d1573 q := by
  simp only [d1573, h 182 (by decide), agree343 p q h, agree103 p q h]
theorem nonnegative1573 (p : Pattern) : 0 ≤ d1573 p :=
  nonnegative_ite (p 182) (nonnegative343 p) (nonnegative103 p)
def d1574 (p : Pattern) : Int := if p 163 then d1573 p else d1572 p
theorem agree1574 (p q : Pattern) (h : Agree support p q) : d1574 p = d1574 q := by
  simp only [d1574, h 163 (by decide), agree1573 p q h, agree1572 p q h]
theorem nonnegative1574 (p : Pattern) : 0 ≤ d1574 p :=
  nonnegative_ite (p 163) (nonnegative1573 p) (nonnegative1572 p)
def d1575 (p : Pattern) : Int := if p 162 then d126 p else d1574 p
theorem agree1575 (p q : Pattern) (h : Agree support p q) : d1575 p = d1575 q := by
  simp only [d1575, h 162 (by decide), agree126 p q h, agree1574 p q h]
theorem nonnegative1575 (p : Pattern) : 0 ≤ d1575 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative1574 p)
def d1576 (p : Pattern) : Int := if p 161 then d129 p else d1575 p
theorem agree1576 (p q : Pattern) (h : Agree support p q) : d1576 p = d1576 q := by
  simp only [d1576, h 161 (by decide), agree129 p q h, agree1575 p q h]
theorem nonnegative1576 (p : Pattern) : 0 ≤ d1576 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative1575 p)
def d1577 (p : Pattern) : Int := if p 162 then d126 p else d124 p
theorem agree1577 (p q : Pattern) (h : Agree support p q) : d1577 p = d1577 q := by
  simp only [d1577, h 162 (by decide), agree126 p q h, agree124 p q h]
theorem nonnegative1577 (p : Pattern) : 0 ≤ d1577 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative124 p)
def d1578 (p : Pattern) : Int := if p 161 then d129 p else d1577 p
theorem agree1578 (p q : Pattern) (h : Agree support p q) : d1578 p = d1578 q := by
  simp only [d1578, h 161 (by decide), agree129 p q h, agree1577 p q h]
theorem nonnegative1578 (p : Pattern) : 0 ≤ d1578 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative1577 p)
def d1579 (p : Pattern) : Int := if p 160 then d1578 p else d1576 p
theorem agree1579 (p q : Pattern) (h : Agree support p q) : d1579 p = d1579 q := by
  simp only [d1579, h 160 (by decide), agree1578 p q h, agree1576 p q h]
theorem nonnegative1579 (p : Pattern) : 0 ≤ d1579 p :=
  nonnegative_ite (p 160) (nonnegative1578 p) (nonnegative1576 p)
def d1580 (p : Pattern) : Int := if p 182 then d336 p else d103 p
theorem agree1580 (p q : Pattern) (h : Agree support p q) : d1580 p = d1580 q := by
  simp only [d1580, h 182 (by decide), agree336 p q h, agree103 p q h]
theorem nonnegative1580 (p : Pattern) : 0 ≤ d1580 p :=
  nonnegative_ite (p 182) (nonnegative336 p) (nonnegative103 p)
def d1581 (p : Pattern) : Int := if p 163 then d139 p else d1580 p
theorem agree1581 (p q : Pattern) (h : Agree support p q) : d1581 p = d1581 q := by
  simp only [d1581, h 163 (by decide), agree139 p q h, agree1580 p q h]
theorem nonnegative1581 (p : Pattern) : 0 ≤ d1581 p :=
  nonnegative_ite (p 163) (nonnegative139 p) (nonnegative1580 p)
def d1582 (p : Pattern) : Int := if p 162 then d141 p else d1581 p
theorem agree1582 (p q : Pattern) (h : Agree support p q) : d1582 p = d1582 q := by
  simp only [d1582, h 162 (by decide), agree141 p q h, agree1581 p q h]
theorem nonnegative1582 (p : Pattern) : 0 ≤ d1582 p :=
  nonnegative_ite (p 162) (nonnegative141 p) (nonnegative1581 p)
def d1583 (p : Pattern) : Int := if p 161 then d144 p else d1582 p
theorem agree1583 (p q : Pattern) (h : Agree support p q) : d1583 p = d1583 q := by
  simp only [d1583, h 161 (by decide), agree144 p q h, agree1582 p q h]
theorem nonnegative1583 (p : Pattern) : 0 ≤ d1583 p :=
  nonnegative_ite (p 161) (nonnegative144 p) (nonnegative1582 p)
def d1584 (p : Pattern) : Int := if p 163 then d139 p else d124 p
theorem agree1584 (p q : Pattern) (h : Agree support p q) : d1584 p = d1584 q := by
  simp only [d1584, h 163 (by decide), agree139 p q h, agree124 p q h]
theorem nonnegative1584 (p : Pattern) : 0 ≤ d1584 p :=
  nonnegative_ite (p 163) (nonnegative139 p) (nonnegative124 p)
def d1585 (p : Pattern) : Int := if p 162 then d141 p else d1584 p
theorem agree1585 (p q : Pattern) (h : Agree support p q) : d1585 p = d1585 q := by
  simp only [d1585, h 162 (by decide), agree141 p q h, agree1584 p q h]
theorem nonnegative1585 (p : Pattern) : 0 ≤ d1585 p :=
  nonnegative_ite (p 162) (nonnegative141 p) (nonnegative1584 p)
def d1586 (p : Pattern) : Int := if p 161 then d144 p else d1585 p
theorem agree1586 (p q : Pattern) (h : Agree support p q) : d1586 p = d1586 q := by
  simp only [d1586, h 161 (by decide), agree144 p q h, agree1585 p q h]
theorem nonnegative1586 (p : Pattern) : 0 ≤ d1586 p :=
  nonnegative_ite (p 161) (nonnegative144 p) (nonnegative1585 p)
def d1587 (p : Pattern) : Int := if p 160 then d1586 p else d1583 p
theorem agree1587 (p q : Pattern) (h : Agree support p q) : d1587 p = d1587 q := by
  simp only [d1587, h 160 (by decide), agree1586 p q h, agree1583 p q h]
theorem nonnegative1587 (p : Pattern) : 0 ≤ d1587 p :=
  nonnegative_ite (p 160) (nonnegative1586 p) (nonnegative1583 p)
def d1588 (p : Pattern) : Int := if p 141 then d1587 p else d1579 p
theorem agree1588 (p q : Pattern) (h : Agree support p q) : d1588 p = d1588 q := by
  simp only [d1588, h 141 (by decide), agree1587 p q h, agree1579 p q h]
theorem nonnegative1588 (p : Pattern) : 0 ≤ d1588 p :=
  nonnegative_ite (p 141) (nonnegative1587 p) (nonnegative1579 p)
def d1589 (p : Pattern) : Int := if p 161 then d12 p else d1054 p
theorem agree1589 (p q : Pattern) (h : Agree support p q) : d1589 p = d1589 q := by
  simp only [d1589, h 161 (by decide), agree12 p q h, agree1054 p q h]
theorem nonnegative1589 (p : Pattern) : 0 ≤ d1589 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1054 p)
def d1590 (p : Pattern) : Int := if p 160 then d1589 p else d1578 p
theorem agree1590 (p q : Pattern) (h : Agree support p q) : d1590 p = d1590 q := by
  simp only [d1590, h 160 (by decide), agree1589 p q h, agree1578 p q h]
theorem nonnegative1590 (p : Pattern) : 0 ≤ d1590 p :=
  nonnegative_ite (p 160) (nonnegative1589 p) (nonnegative1578 p)
def d1591 (p : Pattern) : Int := if p 161 then d12 p else d231 p
theorem agree1591 (p q : Pattern) (h : Agree support p q) : d1591 p = d1591 q := by
  simp only [d1591, h 161 (by decide), agree12 p q h, agree231 p q h]
theorem nonnegative1591 (p : Pattern) : 0 ≤ d1591 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative231 p)
def d1592 (p : Pattern) : Int := if p 160 then d1591 p else d1586 p
theorem agree1592 (p q : Pattern) (h : Agree support p q) : d1592 p = d1592 q := by
  simp only [d1592, h 160 (by decide), agree1591 p q h, agree1586 p q h]
theorem nonnegative1592 (p : Pattern) : 0 ≤ d1592 p :=
  nonnegative_ite (p 160) (nonnegative1591 p) (nonnegative1586 p)
def d1593 (p : Pattern) : Int := if p 141 then d1592 p else d1590 p
theorem agree1593 (p q : Pattern) (h : Agree support p q) : d1593 p = d1593 q := by
  simp only [d1593, h 141 (by decide), agree1592 p q h, agree1590 p q h]
theorem nonnegative1593 (p : Pattern) : 0 ≤ d1593 p :=
  nonnegative_ite (p 141) (nonnegative1592 p) (nonnegative1590 p)
def d1594 (p : Pattern) : Int := if p 138 then d1593 p else d1588 p
theorem agree1594 (p q : Pattern) (h : Agree support p q) : d1594 p = d1594 q := by
  simp only [d1594, h 138 (by decide), agree1593 p q h, agree1588 p q h]
theorem nonnegative1594 (p : Pattern) : 0 ≤ d1594 p :=
  nonnegative_ite (p 138) (nonnegative1593 p) (nonnegative1588 p)
def d1595 (p : Pattern) : Int := if p 162 then d12 p else d128 p
theorem agree1595 (p q : Pattern) (h : Agree support p q) : d1595 p = d1595 q := by
  simp only [d1595, h 162 (by decide), agree12 p q h, agree128 p q h]
theorem nonnegative1595 (p : Pattern) : 0 ≤ d1595 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative128 p)
def d1596 (p : Pattern) : Int := if p 161 then d12 p else d1595 p
theorem agree1596 (p q : Pattern) (h : Agree support p q) : d1596 p = d1596 q := by
  simp only [d1596, h 161 (by decide), agree12 p q h, agree1595 p q h]
theorem nonnegative1596 (p : Pattern) : 0 ≤ d1596 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1595 p)
def d1597 (p : Pattern) : Int := if p 160 then d12 p else d1596 p
theorem agree1597 (p q : Pattern) (h : Agree support p q) : d1597 p = d1597 q := by
  simp only [d1597, h 160 (by decide), agree12 p q h, agree1596 p q h]
theorem nonnegative1597 (p : Pattern) : 0 ≤ d1597 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative1596 p)
def d1598 (p : Pattern) : Int := if p 141 then d12 p else d1597 p
theorem agree1598 (p q : Pattern) (h : Agree support p q) : d1598 p = d1598 q := by
  simp only [d1598, h 141 (by decide), agree12 p q h, agree1597 p q h]
theorem nonnegative1598 (p : Pattern) : 0 ≤ d1598 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative1597 p)
def d1599 (p : Pattern) : Int := if p 138 then d1598 p else d1593 p
theorem agree1599 (p q : Pattern) (h : Agree support p q) : d1599 p = d1599 q := by
  simp only [d1599, h 138 (by decide), agree1598 p q h, agree1593 p q h]
theorem nonnegative1599 (p : Pattern) : 0 ≤ d1599 p :=
  nonnegative_ite (p 138) (nonnegative1598 p) (nonnegative1593 p)
def d1600 (p : Pattern) : Int := if p 116 then d1599 p else d1594 p
theorem agree1600 (p q : Pattern) (h : Agree support p q) : d1600 p = d1600 q := by
  simp only [d1600, h 116 (by decide), agree1599 p q h, agree1594 p q h]
theorem nonnegative1600 (p : Pattern) : 0 ≤ d1600 p :=
  nonnegative_ite (p 116) (nonnegative1599 p) (nonnegative1594 p)
def d1601 (p : Pattern) : Int := if p 163 then d124 p else d1573 p
theorem agree1601 (p q : Pattern) (h : Agree support p q) : d1601 p = d1601 q := by
  simp only [d1601, h 163 (by decide), agree124 p q h, agree1573 p q h]
theorem nonnegative1601 (p : Pattern) : 0 ≤ d1601 p :=
  nonnegative_ite (p 163) (nonnegative124 p) (nonnegative1573 p)
def d1602 (p : Pattern) : Int := if p 162 then d126 p else d1601 p
theorem agree1602 (p q : Pattern) (h : Agree support p q) : d1602 p = d1602 q := by
  simp only [d1602, h 162 (by decide), agree126 p q h, agree1601 p q h]
theorem nonnegative1602 (p : Pattern) : 0 ≤ d1602 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative1601 p)
def d1603 (p : Pattern) : Int := if p 161 then d129 p else d1602 p
theorem agree1603 (p q : Pattern) (h : Agree support p q) : d1603 p = d1603 q := by
  simp only [d1603, h 161 (by decide), agree129 p q h, agree1602 p q h]
theorem nonnegative1603 (p : Pattern) : 0 ≤ d1603 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative1602 p)
def d1604 (p : Pattern) : Int := if p 160 then d1578 p else d1603 p
theorem agree1604 (p q : Pattern) (h : Agree support p q) : d1604 p = d1604 q := by
  simp only [d1604, h 160 (by decide), agree1578 p q h, agree1603 p q h]
theorem nonnegative1604 (p : Pattern) : 0 ≤ d1604 p :=
  nonnegative_ite (p 160) (nonnegative1578 p) (nonnegative1603 p)
def d1605 (p : Pattern) : Int := if p 141 then d1586 p else d1604 p
theorem agree1605 (p q : Pattern) (h : Agree support p q) : d1605 p = d1605 q := by
  simp only [d1605, h 141 (by decide), agree1586 p q h, agree1604 p q h]
theorem nonnegative1605 (p : Pattern) : 0 ≤ d1605 p :=
  nonnegative_ite (p 141) (nonnegative1586 p) (nonnegative1604 p)
def d1606 (p : Pattern) : Int := if p 138 then d1593 p else d1605 p
theorem agree1606 (p q : Pattern) (h : Agree support p q) : d1606 p = d1606 q := by
  simp only [d1606, h 138 (by decide), agree1593 p q h, agree1605 p q h]
theorem nonnegative1606 (p : Pattern) : 0 ≤ d1606 p :=
  nonnegative_ite (p 138) (nonnegative1593 p) (nonnegative1605 p)
def d1607 (p : Pattern) : Int := if p 138 then d12 p else d1593 p
theorem agree1607 (p q : Pattern) (h : Agree support p q) : d1607 p = d1607 q := by
  simp only [d1607, h 138 (by decide), agree12 p q h, agree1593 p q h]
theorem nonnegative1607 (p : Pattern) : 0 ≤ d1607 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1593 p)
def d1608 (p : Pattern) : Int := if p 116 then d1607 p else d1606 p
theorem agree1608 (p q : Pattern) (h : Agree support p q) : d1608 p = d1608 q := by
  simp only [d1608, h 116 (by decide), agree1607 p q h, agree1606 p q h]
theorem nonnegative1608 (p : Pattern) : 0 ≤ d1608 p :=
  nonnegative_ite (p 116) (nonnegative1607 p) (nonnegative1606 p)
def d1609 (p : Pattern) : Int := if p 115 then d1608 p else d1600 p
theorem agree1609 (p q : Pattern) (h : Agree support p q) : d1609 p = d1609 q := by
  simp only [d1609, h 115 (by decide), agree1608 p q h, agree1600 p q h]
theorem nonnegative1609 (p : Pattern) : 0 ≤ d1609 p :=
  nonnegative_ite (p 115) (nonnegative1608 p) (nonnegative1600 p)
def d1610 (p : Pattern) : Int := if p 71 then d1609 p else d1552 p
theorem agree1610 (p q : Pattern) (h : Agree support p q) : d1610 p = d1610 q := by
  simp only [d1610, h 71 (by decide), agree1609 p q h, agree1552 p q h]
theorem nonnegative1610 (p : Pattern) : 0 ≤ d1610 p :=
  nonnegative_ite (p 71) (nonnegative1609 p) (nonnegative1552 p)
def d1611 (p : Pattern) : Int := if p 49 then d1610 p else d1571 p
theorem agree1611 (p q : Pattern) (h : Agree support p q) : d1611 p = d1611 q := by
  simp only [d1611, h 49 (by decide), agree1610 p q h, agree1571 p q h]
theorem nonnegative1611 (p : Pattern) : 0 ≤ d1611 p :=
  nonnegative_ite (p 49) (nonnegative1610 p) (nonnegative1571 p)
def d1612 (p : Pattern) : Int := if p 162 then d176 p else d66 p
theorem agree1612 (p q : Pattern) (h : Agree support p q) : d1612 p = d1612 q := by
  simp only [d1612, h 162 (by decide), agree176 p q h, agree66 p q h]
theorem nonnegative1612 (p : Pattern) : 0 ≤ d1612 p :=
  nonnegative_ite (p 162) (nonnegative176 p) (nonnegative66 p)
def d1613 (p : Pattern) : Int := if p 161 then d177 p else d1612 p
theorem agree1613 (p q : Pattern) (h : Agree support p q) : d1613 p = d1613 q := by
  simp only [d1613, h 161 (by decide), agree177 p q h, agree1612 p q h]
theorem nonnegative1613 (p : Pattern) : 0 ≤ d1613 p :=
  nonnegative_ite (p 161) (nonnegative177 p) (nonnegative1612 p)
def d1614 (p : Pattern) : Int := if p 160 then d1613 p else d1531 p
theorem agree1614 (p q : Pattern) (h : Agree support p q) : d1614 p = d1614 q := by
  simp only [d1614, h 160 (by decide), agree1613 p q h, agree1531 p q h]
theorem nonnegative1614 (p : Pattern) : 0 ≤ d1614 p :=
  nonnegative_ite (p 160) (nonnegative1613 p) (nonnegative1531 p)
def d1615 (p : Pattern) : Int := if p 163 then d43 p else d66 p
theorem agree1615 (p q : Pattern) (h : Agree support p q) : d1615 p = d1615 q := by
  simp only [d1615, h 163 (by decide), agree43 p q h, agree66 p q h]
theorem nonnegative1615 (p : Pattern) : 0 ≤ d1615 p :=
  nonnegative_ite (p 163) (nonnegative43 p) (nonnegative66 p)
def d1616 (p : Pattern) : Int := if p 162 then d181 p else d1615 p
theorem agree1616 (p q : Pattern) (h : Agree support p q) : d1616 p = d1616 q := by
  simp only [d1616, h 162 (by decide), agree181 p q h, agree1615 p q h]
theorem nonnegative1616 (p : Pattern) : 0 ≤ d1616 p :=
  nonnegative_ite (p 162) (nonnegative181 p) (nonnegative1615 p)
def d1617 (p : Pattern) : Int := if p 161 then d184 p else d1616 p
theorem agree1617 (p q : Pattern) (h : Agree support p q) : d1617 p = d1617 q := by
  simp only [d1617, h 161 (by decide), agree184 p q h, agree1616 p q h]
theorem nonnegative1617 (p : Pattern) : 0 ≤ d1617 p :=
  nonnegative_ite (p 161) (nonnegative184 p) (nonnegative1616 p)
def d1618 (p : Pattern) : Int := if p 160 then d1617 p else d1520 p
theorem agree1618 (p q : Pattern) (h : Agree support p q) : d1618 p = d1618 q := by
  simp only [d1618, h 160 (by decide), agree1617 p q h, agree1520 p q h]
theorem nonnegative1618 (p : Pattern) : 0 ≤ d1618 p :=
  nonnegative_ite (p 160) (nonnegative1617 p) (nonnegative1520 p)
def d1619 (p : Pattern) : Int := if p 141 then d1618 p else d1614 p
theorem agree1619 (p q : Pattern) (h : Agree support p q) : d1619 p = d1619 q := by
  simp only [d1619, h 141 (by decide), agree1618 p q h, agree1614 p q h]
theorem nonnegative1619 (p : Pattern) : 0 ≤ d1619 p :=
  nonnegative_ite (p 141) (nonnegative1618 p) (nonnegative1614 p)
def d1620 (p : Pattern) : Int := if p 162 then d176 p else d46 p
theorem agree1620 (p q : Pattern) (h : Agree support p q) : d1620 p = d1620 q := by
  simp only [d1620, h 162 (by decide), agree176 p q h, agree46 p q h]
theorem nonnegative1620 (p : Pattern) : 0 ≤ d1620 p :=
  nonnegative_ite (p 162) (nonnegative176 p) (nonnegative46 p)
def d1621 (p : Pattern) : Int := if p 161 then d177 p else d1620 p
theorem agree1621 (p q : Pattern) (h : Agree support p q) : d1621 p = d1621 q := by
  simp only [d1621, h 161 (by decide), agree177 p q h, agree1620 p q h]
theorem nonnegative1621 (p : Pattern) : 0 ≤ d1621 p :=
  nonnegative_ite (p 161) (nonnegative177 p) (nonnegative1620 p)
def d1622 (p : Pattern) : Int := if p 182 then d12 p else d191 p
theorem agree1622 (p q : Pattern) (h : Agree support p q) : d1622 p = d1622 q := by
  simp only [d1622, h 182 (by decide), agree12 p q h, agree191 p q h]
theorem nonnegative1622 (p : Pattern) : 0 ≤ d1622 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative191 p)
def d1623 (p : Pattern) : Int := if p 163 then d1622 p else d43 p
theorem agree1623 (p q : Pattern) (h : Agree support p q) : d1623 p = d1623 q := by
  simp only [d1623, h 163 (by decide), agree1622 p q h, agree43 p q h]
theorem nonnegative1623 (p : Pattern) : 0 ≤ d1623 p :=
  nonnegative_ite (p 163) (nonnegative1622 p) (nonnegative43 p)
def d1624 (p : Pattern) : Int := if p 162 then d12 p else d1623 p
theorem agree1624 (p q : Pattern) (h : Agree support p q) : d1624 p = d1624 q := by
  simp only [d1624, h 162 (by decide), agree12 p q h, agree1623 p q h]
theorem nonnegative1624 (p : Pattern) : 0 ≤ d1624 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1623 p)
def d1625 (p : Pattern) : Int := if p 161 then d12 p else d1624 p
theorem agree1625 (p q : Pattern) (h : Agree support p q) : d1625 p = d1625 q := by
  simp only [d1625, h 161 (by decide), agree12 p q h, agree1624 p q h]
theorem nonnegative1625 (p : Pattern) : 0 ≤ d1625 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1624 p)
def d1626 (p : Pattern) : Int := if p 160 then d1625 p else d1621 p
theorem agree1626 (p q : Pattern) (h : Agree support p q) : d1626 p = d1626 q := by
  simp only [d1626, h 160 (by decide), agree1625 p q h, agree1621 p q h]
theorem nonnegative1626 (p : Pattern) : 0 ≤ d1626 p :=
  nonnegative_ite (p 160) (nonnegative1625 p) (nonnegative1621 p)
def d1627 (p : Pattern) : Int := if p 163 then d72 p else d43 p
theorem agree1627 (p q : Pattern) (h : Agree support p q) : d1627 p = d1627 q := by
  simp only [d1627, h 163 (by decide), agree72 p q h, agree43 p q h]
theorem nonnegative1627 (p : Pattern) : 0 ≤ d1627 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative43 p)
def d1628 (p : Pattern) : Int := if p 162 then d1627 p else d66 p
theorem agree1628 (p q : Pattern) (h : Agree support p q) : d1628 p = d1628 q := by
  simp only [d1628, h 162 (by decide), agree1627 p q h, agree66 p q h]
theorem nonnegative1628 (p : Pattern) : 0 ≤ d1628 p :=
  nonnegative_ite (p 162) (nonnegative1627 p) (nonnegative66 p)
def d1629 (p : Pattern) : Int := if p 161 then d184 p else d1628 p
theorem agree1629 (p q : Pattern) (h : Agree support p q) : d1629 p = d1629 q := by
  simp only [d1629, h 161 (by decide), agree184 p q h, agree1628 p q h]
theorem nonnegative1629 (p : Pattern) : 0 ≤ d1629 p :=
  nonnegative_ite (p 161) (nonnegative184 p) (nonnegative1628 p)
def d1630 (p : Pattern) : Int := if p 163 then d12 p else d1622 p
theorem agree1630 (p q : Pattern) (h : Agree support p q) : d1630 p = d1630 q := by
  simp only [d1630, h 163 (by decide), agree12 p q h, agree1622 p q h]
theorem nonnegative1630 (p : Pattern) : 0 ≤ d1630 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1622 p)
def d1631 (p : Pattern) : Int := if p 162 then d12 p else d1630 p
theorem agree1631 (p q : Pattern) (h : Agree support p q) : d1631 p = d1631 q := by
  simp only [d1631, h 162 (by decide), agree12 p q h, agree1630 p q h]
theorem nonnegative1631 (p : Pattern) : 0 ≤ d1631 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1630 p)
def d1632 (p : Pattern) : Int := if p 161 then d12 p else d1631 p
theorem agree1632 (p q : Pattern) (h : Agree support p q) : d1632 p = d1632 q := by
  simp only [d1632, h 161 (by decide), agree12 p q h, agree1631 p q h]
theorem nonnegative1632 (p : Pattern) : 0 ≤ d1632 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1631 p)
def d1633 (p : Pattern) : Int := if p 160 then d1632 p else d1629 p
theorem agree1633 (p q : Pattern) (h : Agree support p q) : d1633 p = d1633 q := by
  simp only [d1633, h 160 (by decide), agree1632 p q h, agree1629 p q h]
theorem nonnegative1633 (p : Pattern) : 0 ≤ d1633 p :=
  nonnegative_ite (p 160) (nonnegative1632 p) (nonnegative1629 p)
def d1634 (p : Pattern) : Int := if p 141 then d1633 p else d1626 p
theorem agree1634 (p q : Pattern) (h : Agree support p q) : d1634 p = d1634 q := by
  simp only [d1634, h 141 (by decide), agree1633 p q h, agree1626 p q h]
theorem nonnegative1634 (p : Pattern) : 0 ≤ d1634 p :=
  nonnegative_ite (p 141) (nonnegative1633 p) (nonnegative1626 p)
def d1635 (p : Pattern) : Int := if p 138 then d1634 p else d1619 p
theorem agree1635 (p q : Pattern) (h : Agree support p q) : d1635 p = d1635 q := by
  simp only [d1635, h 138 (by decide), agree1634 p q h, agree1619 p q h]
theorem nonnegative1635 (p : Pattern) : 0 ≤ d1635 p :=
  nonnegative_ite (p 138) (nonnegative1634 p) (nonnegative1619 p)
def d1636 (p : Pattern) : Int := if p 138 then d12 p else d1634 p
theorem agree1636 (p q : Pattern) (h : Agree support p q) : d1636 p = d1636 q := by
  simp only [d1636, h 138 (by decide), agree12 p q h, agree1634 p q h]
theorem nonnegative1636 (p : Pattern) : 0 ≤ d1636 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1634 p)
def d1637 (p : Pattern) : Int := if p 116 then d1636 p else d1635 p
theorem agree1637 (p q : Pattern) (h : Agree support p q) : d1637 p = d1637 q := by
  simp only [d1637, h 116 (by decide), agree1636 p q h, agree1635 p q h]
theorem nonnegative1637 (p : Pattern) : 0 ≤ d1637 p :=
  nonnegative_ite (p 116) (nonnegative1636 p) (nonnegative1635 p)
def d1638 (p : Pattern) : Int := if p 115 then d1637 p else d1565 p
theorem agree1638 (p q : Pattern) (h : Agree support p q) : d1638 p = d1638 q := by
  simp only [d1638, h 115 (by decide), agree1637 p q h, agree1565 p q h]
theorem nonnegative1638 (p : Pattern) : 0 ≤ d1638 p :=
  nonnegative_ite (p 115) (nonnegative1637 p) (nonnegative1565 p)
def d1639 (p : Pattern) : Int := if p 71 then d1638 p else d1552 p
theorem agree1639 (p q : Pattern) (h : Agree support p q) : d1639 p = d1639 q := by
  simp only [d1639, h 71 (by decide), agree1638 p q h, agree1552 p q h]
theorem nonnegative1639 (p : Pattern) : 0 ≤ d1639 p :=
  nonnegative_ite (p 71) (nonnegative1638 p) (nonnegative1552 p)
def d1640 (p : Pattern) : Int := if p 162 then d215 p else d1581 p
theorem agree1640 (p q : Pattern) (h : Agree support p q) : d1640 p = d1640 q := by
  simp only [d1640, h 162 (by decide), agree215 p q h, agree1581 p q h]
theorem nonnegative1640 (p : Pattern) : 0 ≤ d1640 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative1581 p)
def d1641 (p : Pattern) : Int := if p 161 then d217 p else d1640 p
theorem agree1641 (p q : Pattern) (h : Agree support p q) : d1641 p = d1641 q := by
  simp only [d1641, h 161 (by decide), agree217 p q h, agree1640 p q h]
theorem nonnegative1641 (p : Pattern) : 0 ≤ d1641 p :=
  nonnegative_ite (p 161) (nonnegative217 p) (nonnegative1640 p)
def d1642 (p : Pattern) : Int := if p 162 then d215 p else d1584 p
theorem agree1642 (p q : Pattern) (h : Agree support p q) : d1642 p = d1642 q := by
  simp only [d1642, h 162 (by decide), agree215 p q h, agree1584 p q h]
theorem nonnegative1642 (p : Pattern) : 0 ≤ d1642 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative1584 p)
def d1643 (p : Pattern) : Int := if p 161 then d217 p else d1642 p
theorem agree1643 (p q : Pattern) (h : Agree support p q) : d1643 p = d1643 q := by
  simp only [d1643, h 161 (by decide), agree217 p q h, agree1642 p q h]
theorem nonnegative1643 (p : Pattern) : 0 ≤ d1643 p :=
  nonnegative_ite (p 161) (nonnegative217 p) (nonnegative1642 p)
def d1644 (p : Pattern) : Int := if p 160 then d1643 p else d1641 p
theorem agree1644 (p q : Pattern) (h : Agree support p q) : d1644 p = d1644 q := by
  simp only [d1644, h 160 (by decide), agree1643 p q h, agree1641 p q h]
theorem nonnegative1644 (p : Pattern) : 0 ≤ d1644 p :=
  nonnegative_ite (p 160) (nonnegative1643 p) (nonnegative1641 p)
def d1645 (p : Pattern) : Int := if p 141 then d1644 p else d1579 p
theorem agree1645 (p q : Pattern) (h : Agree support p q) : d1645 p = d1645 q := by
  simp only [d1645, h 141 (by decide), agree1644 p q h, agree1579 p q h]
theorem nonnegative1645 (p : Pattern) : 0 ≤ d1645 p :=
  nonnegative_ite (p 141) (nonnegative1644 p) (nonnegative1579 p)
def d1646 (p : Pattern) : Int := if p 160 then d1591 p else d1643 p
theorem agree1646 (p q : Pattern) (h : Agree support p q) : d1646 p = d1646 q := by
  simp only [d1646, h 160 (by decide), agree1591 p q h, agree1643 p q h]
theorem nonnegative1646 (p : Pattern) : 0 ≤ d1646 p :=
  nonnegative_ite (p 160) (nonnegative1591 p) (nonnegative1643 p)
def d1647 (p : Pattern) : Int := if p 141 then d1646 p else d1590 p
theorem agree1647 (p q : Pattern) (h : Agree support p q) : d1647 p = d1647 q := by
  simp only [d1647, h 141 (by decide), agree1646 p q h, agree1590 p q h]
theorem nonnegative1647 (p : Pattern) : 0 ≤ d1647 p :=
  nonnegative_ite (p 141) (nonnegative1646 p) (nonnegative1590 p)
def d1648 (p : Pattern) : Int := if p 138 then d1647 p else d1645 p
theorem agree1648 (p q : Pattern) (h : Agree support p q) : d1648 p = d1648 q := by
  simp only [d1648, h 138 (by decide), agree1647 p q h, agree1645 p q h]
theorem nonnegative1648 (p : Pattern) : 0 ≤ d1648 p :=
  nonnegative_ite (p 138) (nonnegative1647 p) (nonnegative1645 p)
def d1649 (p : Pattern) : Int := if p 138 then d1598 p else d1647 p
theorem agree1649 (p q : Pattern) (h : Agree support p q) : d1649 p = d1649 q := by
  simp only [d1649, h 138 (by decide), agree1598 p q h, agree1647 p q h]
theorem nonnegative1649 (p : Pattern) : 0 ≤ d1649 p :=
  nonnegative_ite (p 138) (nonnegative1598 p) (nonnegative1647 p)
def d1650 (p : Pattern) : Int := if p 116 then d1649 p else d1648 p
theorem agree1650 (p q : Pattern) (h : Agree support p q) : d1650 p = d1650 q := by
  simp only [d1650, h 116 (by decide), agree1649 p q h, agree1648 p q h]
theorem nonnegative1650 (p : Pattern) : 0 ≤ d1650 p :=
  nonnegative_ite (p 116) (nonnegative1649 p) (nonnegative1648 p)
def d1651 (p : Pattern) : Int := if p 162 then d215 p else d139 p
theorem agree1651 (p q : Pattern) (h : Agree support p q) : d1651 p = d1651 q := by
  simp only [d1651, h 162 (by decide), agree215 p q h, agree139 p q h]
theorem nonnegative1651 (p : Pattern) : 0 ≤ d1651 p :=
  nonnegative_ite (p 162) (nonnegative215 p) (nonnegative139 p)
def d1652 (p : Pattern) : Int := if p 161 then d231 p else d1651 p
theorem agree1652 (p q : Pattern) (h : Agree support p q) : d1652 p = d1652 q := by
  simp only [d1652, h 161 (by decide), agree231 p q h, agree1651 p q h]
theorem nonnegative1652 (p : Pattern) : 0 ≤ d1652 p :=
  nonnegative_ite (p 161) (nonnegative231 p) (nonnegative1651 p)
def d1653 (p : Pattern) : Int := if p 160 then d1652 p else d1603 p
theorem agree1653 (p q : Pattern) (h : Agree support p q) : d1653 p = d1653 q := by
  simp only [d1653, h 160 (by decide), agree1652 p q h, agree1603 p q h]
theorem nonnegative1653 (p : Pattern) : 0 ≤ d1653 p :=
  nonnegative_ite (p 160) (nonnegative1652 p) (nonnegative1603 p)
def d1654 (p : Pattern) : Int := if p 162 then d230 p else d125 p
theorem agree1654 (p q : Pattern) (h : Agree support p q) : d1654 p = d1654 q := by
  simp only [d1654, h 162 (by decide), agree230 p q h, agree125 p q h]
theorem nonnegative1654 (p : Pattern) : 0 ≤ d1654 p :=
  nonnegative_ite (p 162) (nonnegative230 p) (nonnegative125 p)
def d1655 (p : Pattern) : Int := if p 161 then d237 p else d1654 p
theorem agree1655 (p q : Pattern) (h : Agree support p q) : d1655 p = d1655 q := by
  simp only [d1655, h 161 (by decide), agree237 p q h, agree1654 p q h]
theorem nonnegative1655 (p : Pattern) : 0 ≤ d1655 p :=
  nonnegative_ite (p 161) (nonnegative237 p) (nonnegative1654 p)
def d1656 (p : Pattern) : Int := if p 160 then d1655 p else d1643 p
theorem agree1656 (p q : Pattern) (h : Agree support p q) : d1656 p = d1656 q := by
  simp only [d1656, h 160 (by decide), agree1655 p q h, agree1643 p q h]
theorem nonnegative1656 (p : Pattern) : 0 ≤ d1656 p :=
  nonnegative_ite (p 160) (nonnegative1655 p) (nonnegative1643 p)
def d1657 (p : Pattern) : Int := if p 141 then d1656 p else d1653 p
theorem agree1657 (p q : Pattern) (h : Agree support p q) : d1657 p = d1657 q := by
  simp only [d1657, h 141 (by decide), agree1656 p q h, agree1653 p q h]
theorem nonnegative1657 (p : Pattern) : 0 ≤ d1657 p :=
  nonnegative_ite (p 141) (nonnegative1656 p) (nonnegative1653 p)
def d1658 (p : Pattern) : Int := if p 163 then d72 p else d139 p
theorem agree1658 (p q : Pattern) (h : Agree support p q) : d1658 p = d1658 q := by
  simp only [d1658, h 163 (by decide), agree72 p q h, agree139 p q h]
theorem nonnegative1658 (p : Pattern) : 0 ≤ d1658 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative139 p)
def d1659 (p : Pattern) : Int := if p 162 then d1658 p else d124 p
theorem agree1659 (p q : Pattern) (h : Agree support p q) : d1659 p = d1659 q := by
  simp only [d1659, h 162 (by decide), agree1658 p q h, agree124 p q h]
theorem nonnegative1659 (p : Pattern) : 0 ≤ d1659 p :=
  nonnegative_ite (p 162) (nonnegative1658 p) (nonnegative124 p)
def d1660 (p : Pattern) : Int := if p 161 then d144 p else d1659 p
theorem agree1660 (p q : Pattern) (h : Agree support p q) : d1660 p = d1660 q := by
  simp only [d1660, h 161 (by decide), agree144 p q h, agree1659 p q h]
theorem nonnegative1660 (p : Pattern) : 0 ≤ d1660 p :=
  nonnegative_ite (p 161) (nonnegative144 p) (nonnegative1659 p)
def d1661 (p : Pattern) : Int := if p 160 then d1591 p else d1660 p
theorem agree1661 (p q : Pattern) (h : Agree support p q) : d1661 p = d1661 q := by
  simp only [d1661, h 160 (by decide), agree1591 p q h, agree1660 p q h]
theorem nonnegative1661 (p : Pattern) : 0 ≤ d1661 p :=
  nonnegative_ite (p 160) (nonnegative1591 p) (nonnegative1660 p)
def d1662 (p : Pattern) : Int := if p 161 then d12 p else d237 p
theorem agree1662 (p q : Pattern) (h : Agree support p q) : d1662 p = d1662 q := by
  simp only [d1662, h 161 (by decide), agree12 p q h, agree237 p q h]
theorem nonnegative1662 (p : Pattern) : 0 ≤ d1662 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative237 p)
def d1663 (p : Pattern) : Int := if p 160 then d1662 p else d1652 p
theorem agree1663 (p q : Pattern) (h : Agree support p q) : d1663 p = d1663 q := by
  simp only [d1663, h 160 (by decide), agree1662 p q h, agree1652 p q h]
theorem nonnegative1663 (p : Pattern) : 0 ≤ d1663 p :=
  nonnegative_ite (p 160) (nonnegative1662 p) (nonnegative1652 p)
def d1664 (p : Pattern) : Int := if p 141 then d1663 p else d1661 p
theorem agree1664 (p q : Pattern) (h : Agree support p q) : d1664 p = d1664 q := by
  simp only [d1664, h 141 (by decide), agree1663 p q h, agree1661 p q h]
theorem nonnegative1664 (p : Pattern) : 0 ≤ d1664 p :=
  nonnegative_ite (p 141) (nonnegative1663 p) (nonnegative1661 p)
def d1665 (p : Pattern) : Int := if p 138 then d1664 p else d1657 p
theorem agree1665 (p q : Pattern) (h : Agree support p q) : d1665 p = d1665 q := by
  simp only [d1665, h 138 (by decide), agree1664 p q h, agree1657 p q h]
theorem nonnegative1665 (p : Pattern) : 0 ≤ d1665 p :=
  nonnegative_ite (p 138) (nonnegative1664 p) (nonnegative1657 p)
def d1666 (p : Pattern) : Int := if p 163 then d48 p else d139 p
theorem agree1666 (p q : Pattern) (h : Agree support p q) : d1666 p = d1666 q := by
  simp only [d1666, h 163 (by decide), agree48 p q h, agree139 p q h]
theorem nonnegative1666 (p : Pattern) : 0 ≤ d1666 p :=
  nonnegative_ite (p 163) (nonnegative48 p) (nonnegative139 p)
def d1667 (p : Pattern) : Int := if p 162 then d1666 p else d124 p
theorem agree1667 (p q : Pattern) (h : Agree support p q) : d1667 p = d1667 q := by
  simp only [d1667, h 162 (by decide), agree1666 p q h, agree124 p q h]
theorem nonnegative1667 (p : Pattern) : 0 ≤ d1667 p :=
  nonnegative_ite (p 162) (nonnegative1666 p) (nonnegative124 p)
def d1668 (p : Pattern) : Int := if p 163 then d48 p else d125 p
theorem agree1668 (p q : Pattern) (h : Agree support p q) : d1668 p = d1668 q := by
  simp only [d1668, h 163 (by decide), agree48 p q h, agree125 p q h]
theorem nonnegative1668 (p : Pattern) : 0 ≤ d1668 p :=
  nonnegative_ite (p 163) (nonnegative48 p) (nonnegative125 p)
def d1669 (p : Pattern) : Int := if p 162 then d12 p else d1668 p
theorem agree1669 (p q : Pattern) (h : Agree support p q) : d1669 p = d1669 q := by
  simp only [d1669, h 162 (by decide), agree12 p q h, agree1668 p q h]
theorem nonnegative1669 (p : Pattern) : 0 ≤ d1669 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1668 p)
def d1670 (p : Pattern) : Int := if p 161 then d1669 p else d1667 p
theorem agree1670 (p q : Pattern) (h : Agree support p q) : d1670 p = d1670 q := by
  simp only [d1670, h 161 (by decide), agree1669 p q h, agree1667 p q h]
theorem nonnegative1670 (p : Pattern) : 0 ≤ d1670 p :=
  nonnegative_ite (p 161) (nonnegative1669 p) (nonnegative1667 p)
def d1671 (p : Pattern) : Int := if p 163 then d72 p else d229 p
theorem agree1671 (p q : Pattern) (h : Agree support p q) : d1671 p = d1671 q := by
  simp only [d1671, h 163 (by decide), agree72 p q h, agree229 p q h]
theorem nonnegative1671 (p : Pattern) : 0 ≤ d1671 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative229 p)
def d1672 (p : Pattern) : Int := if p 162 then d12 p else d1671 p
theorem agree1672 (p q : Pattern) (h : Agree support p q) : d1672 p = d1672 q := by
  simp only [d1672, h 162 (by decide), agree12 p q h, agree1671 p q h]
theorem nonnegative1672 (p : Pattern) : 0 ≤ d1672 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1671 p)
def d1673 (p : Pattern) : Int := if p 161 then d12 p else d1672 p
theorem agree1673 (p q : Pattern) (h : Agree support p q) : d1673 p = d1673 q := by
  simp only [d1673, h 161 (by decide), agree12 p q h, agree1672 p q h]
theorem nonnegative1673 (p : Pattern) : 0 ≤ d1673 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1672 p)
def d1674 (p : Pattern) : Int := if p 160 then d1673 p else d1670 p
theorem agree1674 (p q : Pattern) (h : Agree support p q) : d1674 p = d1674 q := by
  simp only [d1674, h 160 (by decide), agree1673 p q h, agree1670 p q h]
theorem nonnegative1674 (p : Pattern) : 0 ≤ d1674 p :=
  nonnegative_ite (p 160) (nonnegative1673 p) (nonnegative1670 p)
def d1675 (p : Pattern) : Int := if p 141 then d1663 p else d1674 p
theorem agree1675 (p q : Pattern) (h : Agree support p q) : d1675 p = d1675 q := by
  simp only [d1675, h 141 (by decide), agree1663 p q h, agree1674 p q h]
theorem nonnegative1675 (p : Pattern) : 0 ≤ d1675 p :=
  nonnegative_ite (p 141) (nonnegative1663 p) (nonnegative1674 p)
def d1676 (p : Pattern) : Int := if p 138 then d12 p else d1675 p
theorem agree1676 (p q : Pattern) (h : Agree support p q) : d1676 p = d1676 q := by
  simp only [d1676, h 138 (by decide), agree12 p q h, agree1675 p q h]
theorem nonnegative1676 (p : Pattern) : 0 ≤ d1676 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1675 p)
def d1677 (p : Pattern) : Int := if p 116 then d1676 p else d1665 p
theorem agree1677 (p q : Pattern) (h : Agree support p q) : d1677 p = d1677 q := by
  simp only [d1677, h 116 (by decide), agree1676 p q h, agree1665 p q h]
theorem nonnegative1677 (p : Pattern) : 0 ≤ d1677 p :=
  nonnegative_ite (p 116) (nonnegative1676 p) (nonnegative1665 p)
def d1678 (p : Pattern) : Int := if p 115 then d1677 p else d1650 p
theorem agree1678 (p q : Pattern) (h : Agree support p q) : d1678 p = d1678 q := by
  simp only [d1678, h 115 (by decide), agree1677 p q h, agree1650 p q h]
theorem nonnegative1678 (p : Pattern) : 0 ≤ d1678 p :=
  nonnegative_ite (p 115) (nonnegative1677 p) (nonnegative1650 p)
def d1679 (p : Pattern) : Int := if p 71 then d1678 p else d1552 p
theorem agree1679 (p q : Pattern) (h : Agree support p q) : d1679 p = d1679 q := by
  simp only [d1679, h 71 (by decide), agree1678 p q h, agree1552 p q h]
theorem nonnegative1679 (p : Pattern) : 0 ≤ d1679 p :=
  nonnegative_ite (p 71) (nonnegative1678 p) (nonnegative1552 p)
end NetHack.Sokoban22Refined85
