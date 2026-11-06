/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions48
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s7350 (pattern : Twelve) : d1342 (change pattern 12 0) = d1342 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1336 (change pattern 12 0)) = d1342 pattern
  rw [s6278, s7349]
  rfl
theorem s7351 (pattern : Twelve) : d1347 (change pattern 12 0) = d1347 pattern := by
  change (if pattern.e then d1342 (change pattern 12 0) else d1341 (change pattern 12 0)) = d1347 pattern
  rw [s7350, s7347]
  rfl
theorem s7352 (pattern : Twelve) : d1330 (change pattern 12 0) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d1276 (change pattern 12 0)) = d1330 pattern
  rw [s6278, s6444]
  rfl
theorem s7353 (pattern : Twelve) : d1331 (change pattern 12 0) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d1277 (change pattern 12 0)) = d1331 pattern
  rw [s6278, s6459]
  rfl
theorem s7354 (pattern : Twelve) : d1337 (change pattern 12 0) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 12 0) else d1330 (change pattern 12 0)) = d1337 pattern
  rw [s7353, s7352]
  rfl
theorem s7355 (pattern : Twelve) : d1343 (change pattern 12 0) = d1343 pattern := by
  change (if pattern.f then d1337 (change pattern 12 0) else d830 (change pattern 12 0)) = d1343 pattern
  rw [s7354, s6402]
  rfl
theorem s7356 (pattern : Twelve) : d1332 (change pattern 12 0) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d25 (change pattern 12 0)) = d1332 pattern
  rw [s6296, s6331]
  rfl
theorem s7357 (pattern : Twelve) : d1338 (change pattern 12 0) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 12 0) else d1332 (change pattern 12 0)) = d1338 pattern
  rw [s6503, s7356]
  rfl
theorem s7358 (pattern : Twelve) : d1344 (change pattern 12 0) = d1344 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1338 (change pattern 12 0)) = d1344 pattern
  rw [s6278, s7357]
  rfl
theorem s7359 (pattern : Twelve) : d1348 (change pattern 12 0) = d1348 pattern := by
  change (if pattern.e then d1344 (change pattern 12 0) else d1343 (change pattern 12 0)) = d1348 pattern
  rw [s7358, s7355]
  rfl
theorem s7360 (pattern : Twelve) : d1350 (change pattern 12 0) = d1350 pattern := by
  change (if pattern.j then d1348 (change pattern 12 0) else d1347 (change pattern 12 0)) = d1350 pattern
  rw [s7359, s7351]
  rfl
theorem s7361 (pattern : Twelve) : d1351 (change pattern 12 0) = d1351 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1346 (change pattern 12 0)) = d1351 pattern
  rw [s6278, s7343]
  rfl
theorem s7362 (pattern : Twelve) : d1352 (change pattern 12 0) = d1352 pattern := by
  change (if pattern.d then d1351 (change pattern 12 0) else d1350 (change pattern 12 0)) = d1352 pattern
  rw [s7361, s7360]
  rfl
theorem s7363 (pattern : Twelve) : d1353 (change pattern 12 0) = d1353 pattern := by
  change (if pattern.c then d1352 (change pattern 12 0) else d1349 (change pattern 12 0)) = d1353 pattern
  rw [s7362, s7344]
  rfl
theorem s7364 (pattern : Twelve) : d1616 (change pattern 12 0) = d1616 pattern := by
  change (if pattern.i then d119 (change pattern 12 0) else d1276 (change pattern 12 0)) = d1616 pattern
  rw [s6453, s6444]
  rfl
theorem s7365 (pattern : Twelve) : d1619 (change pattern 12 0) = d1619 pattern := by
  change (if pattern.h then d119 (change pattern 12 0) else d1616 (change pattern 12 0)) = d1619 pattern
  rw [s6453, s7364]
  rfl
theorem s7366 (pattern : Twelve) : d1622 (change pattern 12 0) = d1622 pattern := by
  change (if pattern.f then d1619 (change pattern 12 0) else d23 (change pattern 12 0)) = d1622 pattern
  rw [s7365, s6299]
  rfl
theorem s7367 (pattern : Twelve) : d1617 (change pattern 12 0) = d1617 pattern := by
  change (if pattern.i then d24 (change pattern 12 0) else d25 (change pattern 12 0)) = d1617 pattern
  rw [s6328, s6331]
  rfl
theorem s7368 (pattern : Twelve) : d1623 (change pattern 12 0) = d1623 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1617 (change pattern 12 0)) = d1623 pattern
  rw [s6278, s7367]
  rfl
theorem s7369 (pattern : Twelve) : d1627 (change pattern 12 0) = d1627 pattern := by
  change (if pattern.e then d1623 (change pattern 12 0) else d1622 (change pattern 12 0)) = d1627 pattern
  rw [s7368, s7366]
  rfl
theorem s7370 (pattern : Twelve) : d1630 (change pattern 12 0) = d1630 pattern := by
  change (if pattern.j then d1312 (change pattern 12 0) else d1627 (change pattern 12 0)) = d1630 pattern
  rw [s6483, s7369]
  rfl
theorem s7371 (pattern : Twelve) : d1618 (change pattern 12 0) = d1618 pattern := by
  change (if pattern.i then d118 (change pattern 12 0) else d119 (change pattern 12 0)) = d1618 pattern
  rw [s7237, s6453]
  rfl
theorem s7372 (pattern : Twelve) : d1620 (change pattern 12 0) = d1620 pattern := by
  change (if pattern.h then d1618 (change pattern 12 0) else d1282 (change pattern 12 0)) = d1620 pattern
  rw [s7371, s6460]
  rfl
theorem s7373 (pattern : Twelve) : d1624 (change pattern 12 0) = d1624 pattern := by
  change (if pattern.f then d1620 (change pattern 12 0) else d41 (change pattern 12 0)) = d1624 pattern
  rw [s7372, s6329]
  rfl
theorem s7374 (pattern : Twelve) : d1628 (change pattern 12 0) = d1628 pattern := by
  change (if pattern.e then d1304 (change pattern 12 0) else d1624 (change pattern 12 0)) = d1628 pattern
  rw [s6482, s7373]
  rfl
theorem s7375 (pattern : Twelve) : d182 (change pattern 12 0) = d182 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d118 (change pattern 12 0)) = d182 pattern
  rw [s6278, s7237]
  rfl
theorem s7376 (pattern : Twelve) : d1621 (change pattern 12 0) = d1621 pattern := by
  change (if pattern.h then d182 (change pattern 12 0) else d1331 (change pattern 12 0)) = d1621 pattern
  rw [s7375, s7353]
  rfl
theorem s7377 (pattern : Twelve) : d1625 (change pattern 12 0) = d1625 pattern := by
  change (if pattern.f then d1621 (change pattern 12 0) else d49 (change pattern 12 0)) = d1625 pattern
  rw [s7376, s6369]
  rfl
theorem s7378 (pattern : Twelve) : d1626 (change pattern 12 0) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1252 (change pattern 12 0)) = d1626 pattern
  rw [s6278, s7326]
  rfl
theorem s7379 (pattern : Twelve) : d1629 (change pattern 12 0) = d1629 pattern := by
  change (if pattern.e then d1626 (change pattern 12 0) else d1625 (change pattern 12 0)) = d1629 pattern
  rw [s7378, s7377]
  rfl
theorem s7380 (pattern : Twelve) : d1631 (change pattern 12 0) = d1631 pattern := by
  change (if pattern.j then d1629 (change pattern 12 0) else d1628 (change pattern 12 0)) = d1631 pattern
  rw [s7379, s7374]
  rfl
theorem s7381 (pattern : Twelve) : d1632 (change pattern 12 0) = d1632 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1312 (change pattern 12 0)) = d1632 pattern
  rw [s6278, s6483]
  rfl
theorem s7382 (pattern : Twelve) : d1633 (change pattern 12 0) = d1633 pattern := by
  change (if pattern.d then d1632 (change pattern 12 0) else d1631 (change pattern 12 0)) = d1633 pattern
  rw [s7381, s7380]
  rfl
theorem s7383 (pattern : Twelve) : d1634 (change pattern 12 0) = d1634 pattern := by
  change (if pattern.c then d1633 (change pattern 12 0) else d1630 (change pattern 12 0)) = d1634 pattern
  rw [s7382, s7370]
  rfl
theorem s7384 (pattern : Twelve) : d1635 (change pattern 12 0) = d1635 pattern := by
  change (if pattern.g then d1634 (change pattern 12 0) else d1353 (change pattern 12 0)) = d1635 pattern
  rw [s7383, s7363]
  rfl
theorem s7385 (pattern : Twelve) : d1636 (change pattern 12 0) = d1635 pattern := by
  change d1635 (change pattern 12 0) = d1635 pattern
  exact s7384 pattern
theorem s7386 (pattern : Twelve) : d1668 (change pattern 12 0) = d1668 pattern := by
  change (if pattern.f then d1644 (change pattern 12 0) else d19 (change pattern 12 0)) = d1668 pattern
  rw [s6493, s6277]
  rfl
theorem s7387 (pattern : Twelve) : d1671 (change pattern 12 0) = d1671 pattern := by
  change (if pattern.e then d1650 (change pattern 12 0) else d1668 (change pattern 12 0)) = d1671 pattern
  rw [s6491, s7386]
  rfl
theorem s7388 (pattern : Twelve) : d1674 (change pattern 12 0) = d1674 pattern := by
  change (if pattern.j then d1657 (change pattern 12 0) else d1671 (change pattern 12 0)) = d1674 pattern
  rw [s6497, s7387]
  rfl
theorem s7389 (pattern : Twelve) : d1665 (change pattern 12 0) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d1324 (change pattern 12 0)) = d1665 pattern
  rw [s6296, s6489]
  rfl
theorem s7390 (pattern : Twelve) : d1666 (change pattern 12 0) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 12 0) else d1644 (change pattern 12 0)) = d1666 pattern
  rw [s7389, s6493]
  rfl
theorem s7391 (pattern : Twelve) : d1669 (change pattern 12 0) = d1669 pattern := by
  change (if pattern.f then d1666 (change pattern 12 0) else d817 (change pattern 12 0)) = d1669 pattern
  rw [s7390, s6382]
  rfl
theorem s7392 (pattern : Twelve) : d1672 (change pattern 12 0) = d1672 pattern := by
  change (if pattern.e then d1300 (change pattern 12 0) else d1669 (change pattern 12 0)) = d1672 pattern
  rw [s6465, s7391]
  rfl
theorem s7393 (pattern : Twelve) : d183 (change pattern 12 0) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d22 (change pattern 12 0)) = d183 pattern
  rw [s6278, s6296]
  rfl
theorem s7394 (pattern : Twelve) : d1667 (change pattern 12 0) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 12 0) else d128 (change pattern 12 0)) = d1667 pattern
  rw [s7393, s6503]
  rfl
theorem s7395 (pattern : Twelve) : d1670 (change pattern 12 0) = d1670 pattern := by
  change (if pattern.f then d1667 (change pattern 12 0) else d1289 (change pattern 12 0)) = d1670 pattern
  rw [s7394, s6464]
  rfl
theorem s7396 (pattern : Twelve) : d1673 (change pattern 12 0) = d1673 pattern := by
  change (if pattern.e then d1626 (change pattern 12 0) else d1670 (change pattern 12 0)) = d1673 pattern
  rw [s7378, s7395]
  rfl
theorem s7397 (pattern : Twelve) : d1675 (change pattern 12 0) = d1675 pattern := by
  change (if pattern.j then d1673 (change pattern 12 0) else d1672 (change pattern 12 0)) = d1675 pattern
  rw [s7396, s7392]
  rfl
theorem s7398 (pattern : Twelve) : d1676 (change pattern 12 0) = d1676 pattern := by
  change (if pattern.d then d1662 (change pattern 12 0) else d1675 (change pattern 12 0)) = d1676 pattern
  rw [s6509, s7397]
  rfl
theorem s7399 (pattern : Twelve) : d1677 (change pattern 12 0) = d1677 pattern := by
  change (if pattern.c then d1676 (change pattern 12 0) else d1674 (change pattern 12 0)) = d1677 pattern
  rw [s7398, s7388]
  rfl
theorem s7400 (pattern : Twelve) : d1814 (change pattern 12 0) = d1814 pattern := by
  change (if pattern.f then d20 (change pattern 12 0) else d25 (change pattern 12 0)) = d1814 pattern
  rw [s6288, s6331]
  rfl
theorem s7401 (pattern : Twelve) : d1815 (change pattern 12 0) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d21 (change pattern 12 0)) = d1815 pattern
  rw [s6278, s6292]
  rfl
theorem s7402 (pattern : Twelve) : d1818 (change pattern 12 0) = d1818 pattern := by
  change (if pattern.e then d1815 (change pattern 12 0) else d1814 (change pattern 12 0)) = d1818 pattern
  rw [s7401, s7400]
  rfl
theorem s7403 (pattern : Twelve) : d1821 (change pattern 12 0) = d1821 pattern := by
  change (if pattern.j then d1659 (change pattern 12 0) else d1818 (change pattern 12 0)) = d1821 pattern
  rw [s6507, s7402]
  rfl
theorem s7404 (pattern : Twelve) : d1816 (change pattern 12 0) = d1816 pattern := by
  change (if pattern.f then d1646 (change pattern 12 0) else d821 (change pattern 12 0)) = d1816 pattern
  rw [s6502, s6403]
  rfl
theorem s7405 (pattern : Twelve) : d1819 (change pattern 12 0) = d1819 pattern := by
  change (if pattern.e then d1655 (change pattern 12 0) else d1816 (change pattern 12 0)) = d1819 pattern
  rw [s6506, s7404]
  rfl
theorem s7406 (pattern : Twelve) : d1817 (change pattern 12 0) = d1817 pattern := by
  change (if pattern.f then d183 (change pattern 12 0) else d822 (change pattern 12 0)) = d1817 pattern
  rw [s7393, s6404]
  rfl
theorem s7407 (pattern : Twelve) : d1820 (change pattern 12 0) = d1820 pattern := by
  change (if pattern.e then d6 (change pattern 12 0) else d1817 (change pattern 12 0)) = d1820 pattern
  rw [s6278, s7406]
  rfl
theorem s7408 (pattern : Twelve) : d1822 (change pattern 12 0) = d1822 pattern := by
  change (if pattern.j then d1820 (change pattern 12 0) else d1819 (change pattern 12 0)) = d1822 pattern
  rw [s7407, s7405]
  rfl
theorem s7409 (pattern : Twelve) : d1823 (change pattern 12 0) = d1823 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1659 (change pattern 12 0)) = d1823 pattern
  rw [s6278, s6507]
  rfl
theorem s7410 (pattern : Twelve) : d1824 (change pattern 12 0) = d1824 pattern := by
  change (if pattern.d then d1823 (change pattern 12 0) else d1822 (change pattern 12 0)) = d1824 pattern
  rw [s7409, s7408]
  rfl
theorem s7411 (pattern : Twelve) : d1825 (change pattern 12 0) = d1825 pattern := by
  change (if pattern.c then d1824 (change pattern 12 0) else d1821 (change pattern 12 0)) = d1825 pattern
  rw [s7410, s7403]
  rfl
theorem s7412 (pattern : Twelve) : d1826 (change pattern 12 0) = d1826 pattern := by
  change (if pattern.g then d1825 (change pattern 12 0) else d1677 (change pattern 12 0)) = d1826 pattern
  rw [s7411, s7399]
  rfl
theorem s7413 (pattern : Twelve) : d1827 (change pattern 12 0) = d1826 pattern := by
  change d1826 (change pattern 12 0) = d1826 pattern
  exact s7412 pattern
end NetHack.Sokoban21.Diagram
