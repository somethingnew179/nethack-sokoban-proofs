/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions71
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8640 (p : Pattern) : d141 (change p 182 (some 160)) = d4519 p := by
  change (if p 163 then d70 (change p 182 (some 160)) else d125 (change p 182 (some 160))) = d4519 p
  rw [sub8569, sub8628]
  rfl
theorem sub8641 (p : Pattern) : d1585 (change p 182 (some 160)) = d4520 p := by
  change (if p 162 then d141 (change p 182 (some 160)) else d1584 (change p 182 (some 160))) = d4520 p
  rw [sub8640, sub8639]
  rfl
theorem sub8642 (p : Pattern) : d143 (change p 182 (some 160)) = d4521 p := by
  change (if p 163 then d72 (change p 182 (some 160)) else d125 (change p 182 (some 160))) = d4521 p
  rw [sub8574, sub8628]
  rfl
theorem sub8643 (p : Pattern) : d144 (change p 182 (some 160)) = d4522 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d143 (change p 182 (some 160))) = d4522 p
  rw [sub8541, sub8642]
  rfl
theorem sub8644 (p : Pattern) : d1586 (change p 182 (some 160)) = d4523 p := by
  change (if p 161 then d144 (change p 182 (some 160)) else d1585 (change p 182 (some 160))) = d4523 p
  rw [sub8643, sub8641]
  rfl
theorem sub8645 (p : Pattern) : d1587 (change p 182 (some 160)) = d4523 p := by
  change d1586 (change p 182 (some 160)) = d4523 p
  exact sub8644 p
theorem sub8646 (p : Pattern) : d1588 (change p 182 (some 160)) = d4524 p := by
  change (if p 141 then d1587 (change p 182 (some 160)) else d1579 (change p 182 (some 160))) = d4524 p
  rw [sub8645, sub8634]
  rfl
theorem sub8647 (p : Pattern) : d7 (change p 182 (some 160)) = d7 p := by
  rfl
theorem sub8648 (p : Pattern) : d119 (change p 182 (some 160)) = d119 p := by
  change (if p 247 then d12 (change p 182 (some 160)) else d7 (change p 182 (some 160))) = d119 p
  rw [sub8541, sub8647]
  rfl
theorem sub8649 (p : Pattern) : d120 (change p 182 (some 160)) = d120 p := by
  change (if p 246 then d119 (change p 182 (some 160)) else d7 (change p 182 (some 160))) = d120 p
  rw [sub8648, sub8647]
  rfl
theorem sub8650 (p : Pattern) : d229 (change p 182 (some 160)) = d120 p := by
  change d120 (change p 182 (some 160)) = d120 p
  exact sub8649 p
theorem sub8651 (p : Pattern) : d1053 (change p 182 (some 160)) = d4525 p := by
  change (if p 163 then d229 (change p 182 (some 160)) else d139 (change p 182 (some 160))) = d4525 p
  rw [sub8650, sub8638]
  rfl
theorem sub8652 (p : Pattern) : d1054 (change p 182 (some 160)) = d4526 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d1053 (change p 182 (some 160))) = d4526 p
  rw [sub8541, sub8651]
  rfl
theorem sub8653 (p : Pattern) : d1589 (change p 182 (some 160)) = d4527 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d1054 (change p 182 (some 160))) = d4527 p
  rw [sub8541, sub8652]
  rfl
theorem sub8654 (p : Pattern) : d1590 (change p 182 (some 160)) = d4527 p := by
  change d1589 (change p 182 (some 160)) = d4527 p
  exact sub8653 p
theorem sub8655 (p : Pattern) : d230 (change p 182 (some 160)) = d4529 p := by
  change (if p 163 then d12 (change p 182 (some 160)) else d229 (change p 182 (some 160))) = d4529 p
  rw [sub8541, sub8650]
  rfl
theorem sub8656 (p : Pattern) : d231 (change p 182 (some 160)) = d4530 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d230 (change p 182 (some 160))) = d4530 p
  rw [sub8541, sub8655]
  rfl
theorem sub8657 (p : Pattern) : d1591 (change p 182 (some 160)) = d4531 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d231 (change p 182 (some 160))) = d4531 p
  rw [sub8541, sub8656]
  rfl
theorem sub8658 (p : Pattern) : d1592 (change p 182 (some 160)) = d4531 p := by
  change d1591 (change p 182 (some 160)) = d4531 p
  exact sub8657 p
theorem sub8659 (p : Pattern) : d1593 (change p 182 (some 160)) = d5512 p := by
  change (if p 141 then d1592 (change p 182 (some 160)) else d1590 (change p 182 (some 160))) = d5512 p
  rw [sub8658, sub8654]
  rfl
theorem sub8660 (p : Pattern) : d1594 (change p 182 (some 160)) = d5513 p := by
  change (if p 138 then d1593 (change p 182 (some 160)) else d1588 (change p 182 (some 160))) = d5513 p
  rw [sub8659, sub8646]
  rfl
theorem sub8661 (p : Pattern) : d1597 (change p 182 (some 160)) = d12 p := by
  change d12 (change p 182 (some 160)) = d12 p
  exact sub8541 p
theorem sub8662 (p : Pattern) : d1598 (change p 182 (some 160)) = d12 p := by
  change (if p 141 then d12 (change p 182 (some 160)) else d1597 (change p 182 (some 160))) = d12 p
  rw [sub8541, sub8661]
  simp only [ite_self]
theorem sub8663 (p : Pattern) : d1599 (change p 182 (some 160)) = d5514 p := by
  change (if p 138 then d1598 (change p 182 (some 160)) else d1593 (change p 182 (some 160))) = d5514 p
  rw [sub8662, sub8659]
  rfl
theorem sub8664 (p : Pattern) : d1600 (change p 182 (some 160)) = d5515 p := by
  change (if p 116 then d1599 (change p 182 (some 160)) else d1594 (change p 182 (some 160))) = d5515 p
  rw [sub8663, sub8660]
  rfl
theorem sub8665 (p : Pattern) : d1604 (change p 182 (some 160)) = d4517 p := by
  change d1578 (change p 182 (some 160)) = d4517 p
  exact sub8633 p
theorem sub8666 (p : Pattern) : d1605 (change p 182 (some 160)) = d4524 p := by
  change (if p 141 then d1586 (change p 182 (some 160)) else d1604 (change p 182 (some 160))) = d4524 p
  rw [sub8644, sub8665]
  rfl
theorem sub8667 (p : Pattern) : d1606 (change p 182 (some 160)) = d5513 p := by
  change (if p 138 then d1593 (change p 182 (some 160)) else d1605 (change p 182 (some 160))) = d5513 p
  rw [sub8659, sub8666]
  rfl
theorem sub8668 (p : Pattern) : d1607 (change p 182 (some 160)) = d5514 p := by
  change (if p 138 then d12 (change p 182 (some 160)) else d1593 (change p 182 (some 160))) = d5514 p
  rw [sub8541, sub8659]
  rfl
theorem sub8669 (p : Pattern) : d1608 (change p 182 (some 160)) = d5515 p := by
  change (if p 116 then d1607 (change p 182 (some 160)) else d1606 (change p 182 (some 160))) = d5515 p
  rw [sub8668, sub8667]
  rfl
theorem sub8670 (p : Pattern) : d1609 (change p 182 (some 160)) = d5515 p := by
  change (if p 115 then d1608 (change p 182 (some 160)) else d1600 (change p 182 (some 160))) = d5515 p
  rw [sub8669, sub8664]
  simp only [ite_self]
theorem sub8671 (p : Pattern) : d1610 (change p 182 (some 160)) = d5516 p := by
  change (if p 71 then d1609 (change p 182 (some 160)) else d1552 (change p 182 (some 160))) = d5516 p
  rw [sub8670, sub8608]
  rfl
theorem sub8672 (p : Pattern) : d1611 (change p 182 (some 160)) = d5517 p := by
  change (if p 49 then d1610 (change p 182 (some 160)) else d1571 (change p 182 (some 160))) = d5517 p
  rw [sub8671, sub8620]
  rfl
theorem sub8673 (p : Pattern) : d1612 (change p 182 (some 160)) = d4546 p := by
  change (if p 162 then d176 (change p 182 (some 160)) else d66 (change p 182 (some 160))) = d4546 p
  rw [sub8584, sub8562]
  rfl
theorem sub8674 (p : Pattern) : d1613 (change p 182 (some 160)) = d4547 p := by
  change (if p 161 then d177 (change p 182 (some 160)) else d1612 (change p 182 (some 160))) = d4547 p
  rw [sub8585, sub8673]
  rfl
theorem sub8675 (p : Pattern) : d1614 (change p 182 (some 160)) = d4547 p := by
  change d1613 (change p 182 (some 160)) = d4547 p
  exact sub8674 p
theorem sub8676 (p : Pattern) : d1615 (change p 182 (some 160)) = d4549 p := by
  change (if p 163 then d43 (change p 182 (some 160)) else d66 (change p 182 (some 160))) = d4549 p
  rw [sub8548, sub8562]
  rfl
theorem sub8677 (p : Pattern) : d181 (change p 182 (some 160)) = d4550 p := by
  change (if p 163 then d72 (change p 182 (some 160)) else d173 (change p 182 (some 160))) = d4550 p
  rw [sub8574, sub8583]
  rfl
theorem sub8678 (p : Pattern) : d1616 (change p 182 (some 160)) = d4551 p := by
  change (if p 162 then d181 (change p 182 (some 160)) else d1615 (change p 182 (some 160))) = d4551 p
  rw [sub8677, sub8676]
  rfl
theorem sub8679 (p : Pattern) : d1617 (change p 182 (some 160)) = d4552 p := by
  change (if p 161 then d184 (change p 182 (some 160)) else d1616 (change p 182 (some 160))) = d4552 p
  rw [sub8589, sub8678]
  rfl
theorem sub8680 (p : Pattern) : d1618 (change p 182 (some 160)) = d4552 p := by
  change d1617 (change p 182 (some 160)) = d4552 p
  exact sub8679 p
theorem sub8681 (p : Pattern) : d1619 (change p 182 (some 160)) = d5518 p := by
  change (if p 141 then d1618 (change p 182 (some 160)) else d1614 (change p 182 (some 160))) = d5518 p
  rw [sub8680, sub8675]
  rfl
theorem sub8682 (p : Pattern) : d8 (change p 182 (some 160)) = d8 p := by
  rfl
theorem sub8683 (p : Pattern) : d190 (change p 182 (some 160)) = d190 p := by
  change (if p 247 then d12 (change p 182 (some 160)) else d8 (change p 182 (some 160))) = d190 p
  rw [sub8541, sub8682]
  rfl
theorem sub8684 (p : Pattern) : d191 (change p 182 (some 160)) = d191 p := by
  change (if p 246 then d190 (change p 182 (some 160)) else d8 (change p 182 (some 160))) = d191 p
  rw [sub8683, sub8682]
  rfl
theorem sub8685 (p : Pattern) : d1622 (change p 182 (some 160)) = d191 p := by
  change d191 (change p 182 (some 160)) = d191 p
  exact sub8684 p
theorem sub8686 (p : Pattern) : d1623 (change p 182 (some 160)) = d4557 p := by
  change (if p 163 then d1622 (change p 182 (some 160)) else d43 (change p 182 (some 160))) = d4557 p
  rw [sub8685, sub8548]
  rfl
theorem sub8687 (p : Pattern) : d1624 (change p 182 (some 160)) = d4558 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d1623 (change p 182 (some 160))) = d4558 p
  rw [sub8541, sub8686]
  rfl
theorem sub8688 (p : Pattern) : d1625 (change p 182 (some 160)) = d4559 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d1624 (change p 182 (some 160))) = d4559 p
  rw [sub8541, sub8687]
  rfl
theorem sub8689 (p : Pattern) : d1626 (change p 182 (some 160)) = d4559 p := by
  change d1625 (change p 182 (some 160)) = d4559 p
  exact sub8688 p
theorem sub8690 (p : Pattern) : d1630 (change p 182 (some 160)) = d4564 p := by
  change (if p 163 then d12 (change p 182 (some 160)) else d1622 (change p 182 (some 160))) = d4564 p
  rw [sub8541, sub8685]
  rfl
theorem sub8691 (p : Pattern) : d1631 (change p 182 (some 160)) = d4565 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d1630 (change p 182 (some 160))) = d4565 p
  rw [sub8541, sub8690]
  rfl
theorem sub8692 (p : Pattern) : d1632 (change p 182 (some 160)) = d4566 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d1631 (change p 182 (some 160))) = d4566 p
  rw [sub8541, sub8691]
  rfl
theorem sub8693 (p : Pattern) : d1633 (change p 182 (some 160)) = d4566 p := by
  change d1632 (change p 182 (some 160)) = d4566 p
  exact sub8692 p
theorem sub8694 (p : Pattern) : d1634 (change p 182 (some 160)) = d5519 p := by
  change (if p 141 then d1633 (change p 182 (some 160)) else d1626 (change p 182 (some 160))) = d5519 p
  rw [sub8693, sub8689]
  rfl
theorem sub8695 (p : Pattern) : d1635 (change p 182 (some 160)) = d5520 p := by
  change (if p 138 then d1634 (change p 182 (some 160)) else d1619 (change p 182 (some 160))) = d5520 p
  rw [sub8694, sub8681]
  rfl
theorem sub8696 (p : Pattern) : d1636 (change p 182 (some 160)) = d5521 p := by
  change (if p 138 then d12 (change p 182 (some 160)) else d1634 (change p 182 (some 160))) = d5521 p
  rw [sub8541, sub8694]
  rfl
theorem sub8697 (p : Pattern) : d1637 (change p 182 (some 160)) = d5522 p := by
  change (if p 116 then d1636 (change p 182 (some 160)) else d1635 (change p 182 (some 160))) = d5522 p
  rw [sub8696, sub8695]
  rfl
theorem sub8698 (p : Pattern) : d1638 (change p 182 (some 160)) = d5523 p := by
  change (if p 115 then d1637 (change p 182 (some 160)) else d1565 (change p 182 (some 160))) = d5523 p
  rw [sub8697, sub8614]
  rfl
theorem sub8699 (p : Pattern) : d1639 (change p 182 (some 160)) = d5524 p := by
  change (if p 71 then d1638 (change p 182 (some 160)) else d1552 (change p 182 (some 160))) = d5524 p
  rw [sub8698, sub8608]
  rfl
theorem sub8700 (p : Pattern) : d215 (change p 182 (some 160)) = d4574 p := by
  change (if p 163 then d12 (change p 182 (some 160)) else d125 (change p 182 (some 160))) = d4574 p
  rw [sub8541, sub8628]
  rfl
theorem sub8701 (p : Pattern) : d1642 (change p 182 (some 160)) = d4575 p := by
  change (if p 162 then d215 (change p 182 (some 160)) else d1584 (change p 182 (some 160))) = d4575 p
  rw [sub8700, sub8639]
  rfl
theorem sub8702 (p : Pattern) : d217 (change p 182 (some 160)) = d4576 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d215 (change p 182 (some 160))) = d4576 p
  rw [sub8541, sub8700]
  rfl
theorem sub8703 (p : Pattern) : d1643 (change p 182 (some 160)) = d4577 p := by
  change (if p 161 then d217 (change p 182 (some 160)) else d1642 (change p 182 (some 160))) = d4577 p
  rw [sub8702, sub8701]
  rfl
theorem sub8704 (p : Pattern) : d1644 (change p 182 (some 160)) = d4577 p := by
  change d1643 (change p 182 (some 160)) = d4577 p
  exact sub8703 p
theorem sub8705 (p : Pattern) : d1645 (change p 182 (some 160)) = d4578 p := by
  change (if p 141 then d1644 (change p 182 (some 160)) else d1579 (change p 182 (some 160))) = d4578 p
  rw [sub8704, sub8634]
  rfl
theorem sub8706 (p : Pattern) : d1646 (change p 182 (some 160)) = d4531 p := by
  change d1591 (change p 182 (some 160)) = d4531 p
  exact sub8657 p
theorem sub8707 (p : Pattern) : d1647 (change p 182 (some 160)) = d5512 p := by
  change (if p 141 then d1646 (change p 182 (some 160)) else d1590 (change p 182 (some 160))) = d5512 p
  rw [sub8706, sub8654]
  rfl
theorem sub8708 (p : Pattern) : d1648 (change p 182 (some 160)) = d5525 p := by
  change (if p 138 then d1647 (change p 182 (some 160)) else d1645 (change p 182 (some 160))) = d5525 p
  rw [sub8707, sub8705]
  rfl
theorem sub8709 (p : Pattern) : d1649 (change p 182 (some 160)) = d5514 p := by
  change (if p 138 then d1598 (change p 182 (some 160)) else d1647 (change p 182 (some 160))) = d5514 p
  rw [sub8662, sub8707]
  rfl
theorem sub8710 (p : Pattern) : d1650 (change p 182 (some 160)) = d5526 p := by
  change (if p 116 then d1649 (change p 182 (some 160)) else d1648 (change p 182 (some 160))) = d5526 p
  rw [sub8709, sub8708]
  rfl
theorem sub8711 (p : Pattern) : d1651 (change p 182 (some 160)) = d4584 p := by
  change (if p 162 then d215 (change p 182 (some 160)) else d139 (change p 182 (some 160))) = d4584 p
  rw [sub8700, sub8638]
  rfl
theorem sub8712 (p : Pattern) : d1652 (change p 182 (some 160)) = d4585 p := by
  change (if p 161 then d231 (change p 182 (some 160)) else d1651 (change p 182 (some 160))) = d4585 p
  rw [sub8656, sub8711]
  rfl
theorem sub8713 (p : Pattern) : d1653 (change p 182 (some 160)) = d4585 p := by
  change d1652 (change p 182 (some 160)) = d4585 p
  exact sub8712 p
theorem sub8714 (p : Pattern) : d1654 (change p 182 (some 160)) = d4587 p := by
  change (if p 162 then d230 (change p 182 (some 160)) else d125 (change p 182 (some 160))) = d4587 p
  rw [sub8655, sub8628]
  rfl
theorem sub8715 (p : Pattern) : d237 (change p 182 (some 160)) = d4588 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d49 (change p 182 (some 160))) = d4588 p
  rw [sub8541, sub8555]
  rfl
theorem sub8716 (p : Pattern) : d1655 (change p 182 (some 160)) = d4589 p := by
  change (if p 161 then d237 (change p 182 (some 160)) else d1654 (change p 182 (some 160))) = d4589 p
  rw [sub8715, sub8714]
  rfl
theorem sub8717 (p : Pattern) : d1656 (change p 182 (some 160)) = d4589 p := by
  change d1655 (change p 182 (some 160)) = d4589 p
  exact sub8716 p
theorem sub8718 (p : Pattern) : d1657 (change p 182 (some 160)) = d5527 p := by
  change (if p 141 then d1656 (change p 182 (some 160)) else d1653 (change p 182 (some 160))) = d5527 p
  rw [sub8717, sub8713]
  rfl
theorem sub8719 (p : Pattern) : d1661 (change p 182 (some 160)) = d4531 p := by
  change d1591 (change p 182 (some 160)) = d4531 p
  exact sub8657 p
theorem sub8720 (p : Pattern) : d1662 (change p 182 (some 160)) = d4596 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d237 (change p 182 (some 160))) = d4596 p
  rw [sub8541, sub8715]
  rfl
theorem sub8721 (p : Pattern) : d1663 (change p 182 (some 160)) = d4596 p := by
  change d1662 (change p 182 (some 160)) = d4596 p
  exact sub8720 p
theorem sub8722 (p : Pattern) : d1664 (change p 182 (some 160)) = d5528 p := by
  change (if p 141 then d1663 (change p 182 (some 160)) else d1661 (change p 182 (some 160))) = d5528 p
  rw [sub8721, sub8719]
  rfl
theorem sub8723 (p : Pattern) : d1665 (change p 182 (some 160)) = d5529 p := by
  change (if p 138 then d1664 (change p 182 (some 160)) else d1657 (change p 182 (some 160))) = d5529 p
  rw [sub8722, sub8718]
  rfl
theorem sub8724 (p : Pattern) : d1671 (change p 182 (some 160)) = d4605 p := by
  change (if p 163 then d72 (change p 182 (some 160)) else d229 (change p 182 (some 160))) = d4605 p
  rw [sub8574, sub8650]
  rfl
theorem sub8725 (p : Pattern) : d1672 (change p 182 (some 160)) = d4606 p := by
  change (if p 162 then d12 (change p 182 (some 160)) else d1671 (change p 182 (some 160))) = d4606 p
  rw [sub8541, sub8724]
  rfl
theorem sub8726 (p : Pattern) : d1673 (change p 182 (some 160)) = d4607 p := by
  change (if p 161 then d12 (change p 182 (some 160)) else d1672 (change p 182 (some 160))) = d4607 p
  rw [sub8541, sub8725]
  rfl
theorem sub8727 (p : Pattern) : d1674 (change p 182 (some 160)) = d4607 p := by
  change d1673 (change p 182 (some 160)) = d4607 p
  exact sub8726 p
theorem sub8728 (p : Pattern) : d1675 (change p 182 (some 160)) = d5530 p := by
  change (if p 141 then d1663 (change p 182 (some 160)) else d1674 (change p 182 (some 160))) = d5530 p
  rw [sub8721, sub8727]
  rfl
theorem sub8729 (p : Pattern) : d1676 (change p 182 (some 160)) = d5531 p := by
  change (if p 138 then d12 (change p 182 (some 160)) else d1675 (change p 182 (some 160))) = d5531 p
  rw [sub8541, sub8728]
  rfl
theorem sub8730 (p : Pattern) : d1677 (change p 182 (some 160)) = d5532 p := by
  change (if p 116 then d1676 (change p 182 (some 160)) else d1665 (change p 182 (some 160))) = d5532 p
  rw [sub8729, sub8723]
  rfl
theorem sub8731 (p : Pattern) : d1678 (change p 182 (some 160)) = d5533 p := by
  change (if p 115 then d1677 (change p 182 (some 160)) else d1650 (change p 182 (some 160))) = d5533 p
  rw [sub8730, sub8710]
  rfl
theorem sub8732 (p : Pattern) : d1679 (change p 182 (some 160)) = d5534 p := by
  change (if p 71 then d1678 (change p 182 (some 160)) else d1552 (change p 182 (some 160))) = d5534 p
  rw [sub8731, sub8608]
  rfl
theorem sub8733 (p : Pattern) : d1680 (change p 182 (some 160)) = d5535 p := by
  change (if p 49 then d1679 (change p 182 (some 160)) else d1639 (change p 182 (some 160))) = d5535 p
  rw [sub8732, sub8699]
  rfl
theorem sub8734 (p : Pattern) : d1681 (change p 182 (some 160)) = d5536 p := by
  change (if p 48 then d1680 (change p 182 (some 160)) else d1611 (change p 182 (some 160))) = d5536 p
  rw [sub8733, sub8672]
  rfl
theorem sub8735 (p : Pattern) : d1769 (change p 10000 none) = d1769 p := by
  change (if p 247 then d4 (change p 10000 none) else d0 (change p 10000 none)) = d1769 p
  rw [sub6, sub0]
  rfl
theorem sub8736 (p : Pattern) : d1770 (change p 10000 none) = d1770 p := by
  change (if p 246 then d17 (change p 10000 none) else d1769 (change p 10000 none)) = d1770 p
  rw [sub7, sub8735]
  rfl
theorem sub8737 (p : Pattern) : d1771 (change p 10000 none) = d1771 p := by
  change (if p 225 then d1770 (change p 10000 none) else d14 (change p 10000 none)) = d1771 p
  rw [sub8736, sub3]
  rfl
theorem sub8738 (p : Pattern) : d1772 (change p 10000 none) = d1772 p := by
  change (if p 224 then d1770 (change p 10000 none) else d1771 (change p 10000 none)) = d1772 p
  rw [sub8736, sub8737]
  rfl
theorem sub8739 (p : Pattern) : d2895 (change p 10000 none) = d2895 p := by
  change (if p 204 then d1772 (change p 10000 none) else d14 (change p 10000 none)) = d2895 p
  rw [sub8738, sub3]
  rfl
theorem sub8740 (p : Pattern) : d1683 (change p 10000 none) = d1683 p := by
  change (if p 247 then d2 (change p 10000 none) else d0 (change p 10000 none)) = d1683 p
  rw [sub21, sub0]
  rfl
theorem sub8741 (p : Pattern) : d1684 (change p 10000 none) = d1684 p := by
  change (if p 246 then d30 (change p 10000 none) else d1683 (change p 10000 none)) = d1684 p
  rw [sub22, sub8740]
  rfl
theorem sub8742 (p : Pattern) : d1685 (change p 10000 none) = d1685 p := by
  change (if p 225 then d1684 (change p 10000 none) else d14 (change p 10000 none)) = d1685 p
  rw [sub8741, sub3]
  rfl
theorem sub8743 (p : Pattern) : d1686 (change p 10000 none) = d1686 p := by
  change (if p 224 then d1684 (change p 10000 none) else d1685 (change p 10000 none)) = d1686 p
  rw [sub8741, sub8742]
  rfl
theorem sub8744 (p : Pattern) : d1687 (change p 10000 none) = d1687 p := by
  change (if p 204 then d12 (change p 10000 none) else d1686 (change p 10000 none)) = d1687 p
  rw [sub1, sub8743]
  rfl
theorem sub8745 (p : Pattern) : d2896 (change p 10000 none) = d2896 p := by
  change (if p 182 then d1687 (change p 10000 none) else d2895 (change p 10000 none)) = d2896 p
  rw [sub8744, sub8739]
  rfl
theorem sub8746 (p : Pattern) : d1794 (change p 10000 none) = d1794 p := by
  change (if p 247 then d8 (change p 10000 none) else d4 (change p 10000 none)) = d1794 p
  rw [sub189, sub6]
  rfl
theorem sub8747 (p : Pattern) : d1795 (change p 10000 none) = d1795 p := by
  change (if p 246 then d190 (change p 10000 none) else d1794 (change p 10000 none)) = d1795 p
  rw [sub190, sub8746]
  rfl
theorem sub8748 (p : Pattern) : d2011 (change p 10000 none) = d2011 p := by
  change (if p 225 then d1795 (change p 10000 none) else d18 (change p 10000 none)) = d2011 p
  rw [sub8747, sub8]
  rfl
theorem sub8749 (p : Pattern) : d2012 (change p 10000 none) = d2012 p := by
  change (if p 224 then d1795 (change p 10000 none) else d2011 (change p 10000 none)) = d2012 p
  rw [sub8747, sub8748]
  rfl
theorem sub8750 (p : Pattern) : d2897 (change p 10000 none) = d2897 p := by
  change (if p 204 then d2012 (change p 10000 none) else d18 (change p 10000 none)) = d2897 p
  rw [sub8749, sub8]
  rfl
theorem sub8751 (p : Pattern) : d1693 (change p 10000 none) = d1693 p := by
  change (if p 247 then d6 (change p 10000 none) else d4 (change p 10000 none)) = d1693 p
  rw [sub26, sub6]
  rfl
theorem sub8752 (p : Pattern) : d1694 (change p 10000 none) = d1694 p := by
  change (if p 246 then d34 (change p 10000 none) else d1693 (change p 10000 none)) = d1694 p
  rw [sub27, sub8751]
  rfl
theorem sub8753 (p : Pattern) : d1695 (change p 10000 none) = d1695 p := by
  change (if p 225 then d1694 (change p 10000 none) else d18 (change p 10000 none)) = d1695 p
  rw [sub8752, sub8]
  rfl
theorem sub8754 (p : Pattern) : d1696 (change p 10000 none) = d1696 p := by
  change (if p 224 then d1694 (change p 10000 none) else d1695 (change p 10000 none)) = d1696 p
  rw [sub8752, sub8753]
  rfl
theorem sub8755 (p : Pattern) : d1697 (change p 10000 none) = d1697 p := by
  change (if p 204 then d12 (change p 10000 none) else d1696 (change p 10000 none)) = d1697 p
  rw [sub1, sub8754]
  rfl
theorem sub8756 (p : Pattern) : d2898 (change p 10000 none) = d2898 p := by
  change (if p 182 then d1697 (change p 10000 none) else d2897 (change p 10000 none)) = d2898 p
  rw [sub8755, sub8750]
  rfl
theorem sub8757 (p : Pattern) : d2899 (change p 10000 none) = d2899 p := by
  change (if p 163 then d2898 (change p 10000 none) else d2896 (change p 10000 none)) = d2899 p
  rw [sub8756, sub8745]
  rfl
theorem sub8758 (p : Pattern) : d2900 (change p 10000 none) = d2900 p := by
  change (if p 162 then d2899 (change p 10000 none) else d2896 (change p 10000 none)) = d2900 p
  rw [sub8757, sub8745]
  rfl
theorem sub8759 (p : Pattern) : d1802 (change p 10000 none) = d1802 p := by
  change (if p 225 then d356 (change p 10000 none) else d24 (change p 10000 none)) = d1802 p
  rw [sub7830, sub15]
  rfl
end NetHack.Sokoban22Refined85
