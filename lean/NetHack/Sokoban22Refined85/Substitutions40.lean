/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions39
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4800 (p : Pattern) : d1600 (change p 182 (some 204)) = d4540 p := by
  change (if p 116 then d1599 (change p 182 (some 204)) else d1594 (change p 182 (some 204))) = d4540 p
  rw [sub4799, sub4794]
  rfl
theorem sub4801 (p : Pattern) : d1601 (change p 182 (some 204)) = d103 p := by
  change (if p 163 then d124 (change p 182 (some 204)) else d1573 (change p 182 (some 204))) = d103 p
  rw [sub4752, sub4750]
  simp only [ite_self]
theorem sub4802 (p : Pattern) : d1602 (change p 182 (some 204)) = d4514 p := by
  change (if p 162 then d126 (change p 182 (some 204)) else d1601 (change p 182 (some 204))) = d4514 p
  rw [sub4757, sub4801]
  rfl
theorem sub4803 (p : Pattern) : d1603 (change p 182 (some 204)) = d4517 p := by
  change (if p 161 then d129 (change p 182 (some 204)) else d1602 (change p 182 (some 204))) = d4517 p
  rw [sub4760, sub4802]
  rfl
theorem sub4804 (p : Pattern) : d1604 (change p 182 (some 204)) = d4517 p := by
  change (if p 160 then d1578 (change p 182 (some 204)) else d1603 (change p 182 (some 204))) = d4517 p
  rw [sub4763, sub4803]
  simp only [ite_self]
theorem sub4805 (p : Pattern) : d1605 (change p 182 (some 204)) = d4524 p := by
  change (if p 141 then d1586 (change p 182 (some 204)) else d1604 (change p 182 (some 204))) = d4524 p
  rw [sub4778, sub4804]
  rfl
theorem sub4806 (p : Pattern) : d1606 (change p 182 (some 204)) = d4534 p := by
  change (if p 138 then d1593 (change p 182 (some 204)) else d1605 (change p 182 (some 204))) = d4534 p
  rw [sub4793, sub4805]
  rfl
theorem sub4807 (p : Pattern) : d1607 (change p 182 (some 204)) = d4541 p := by
  change (if p 138 then d12 (change p 182 (some 204)) else d1593 (change p 182 (some 204))) = d4541 p
  rw [sub4639, sub4793]
  rfl
theorem sub4808 (p : Pattern) : d1608 (change p 182 (some 204)) = d4542 p := by
  change (if p 116 then d1607 (change p 182 (some 204)) else d1606 (change p 182 (some 204))) = d4542 p
  rw [sub4807, sub4806]
  rfl
theorem sub4809 (p : Pattern) : d1609 (change p 182 (some 204)) = d4543 p := by
  change (if p 115 then d1608 (change p 182 (some 204)) else d1600 (change p 182 (some 204))) = d4543 p
  rw [sub4808, sub4800]
  rfl
theorem sub4810 (p : Pattern) : d1610 (change p 182 (some 204)) = d4544 p := by
  change (if p 71 then d1609 (change p 182 (some 204)) else d1552 (change p 182 (some 204))) = d4544 p
  rw [sub4809, sub4726]
  rfl
theorem sub4811 (p : Pattern) : d1611 (change p 182 (some 204)) = d4545 p := by
  change (if p 49 then d1610 (change p 182 (some 204)) else d1571 (change p 182 (some 204))) = d4545 p
  rw [sub4810, sub4745]
  rfl
theorem sub4812 (p : Pattern) : d1612 (change p 182 (some 204)) = d4546 p := by
  change (if p 162 then d176 (change p 182 (some 204)) else d66 (change p 182 (some 204))) = d4546 p
  rw [sub4693, sub4668]
  rfl
theorem sub4813 (p : Pattern) : d1613 (change p 182 (some 204)) = d4547 p := by
  change (if p 161 then d177 (change p 182 (some 204)) else d1612 (change p 182 (some 204))) = d4547 p
  rw [sub4694, sub4812]
  rfl
theorem sub4814 (p : Pattern) : d1614 (change p 182 (some 204)) = d4548 p := by
  change (if p 160 then d1613 (change p 182 (some 204)) else d1531 (change p 182 (some 204))) = d4548 p
  rw [sub4813, sub4705]
  rfl
theorem sub4815 (p : Pattern) : d1615 (change p 182 (some 204)) = d4549 p := by
  change (if p 163 then d43 (change p 182 (some 204)) else d66 (change p 182 (some 204))) = d4549 p
  rw [sub4649, sub4668]
  rfl
theorem sub4816 (p : Pattern) : d181 (change p 182 (some 204)) = d4550 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d173 (change p 182 (some 204))) = d4550 p
  rw [sub4680, sub4692]
  rfl
theorem sub4817 (p : Pattern) : d1616 (change p 182 (some 204)) = d4551 p := by
  change (if p 162 then d181 (change p 182 (some 204)) else d1615 (change p 182 (some 204))) = d4551 p
  rw [sub4816, sub4815]
  rfl
theorem sub4818 (p : Pattern) : d1617 (change p 182 (some 204)) = d4552 p := by
  change (if p 161 then d184 (change p 182 (some 204)) else d1616 (change p 182 (some 204))) = d4552 p
  rw [sub4698, sub4817]
  rfl
theorem sub4819 (p : Pattern) : d1618 (change p 182 (some 204)) = d4553 p := by
  change (if p 160 then d1617 (change p 182 (some 204)) else d1520 (change p 182 (some 204))) = d4553 p
  rw [sub4818, sub4686]
  rfl
theorem sub4820 (p : Pattern) : d1619 (change p 182 (some 204)) = d4554 p := by
  change (if p 141 then d1618 (change p 182 (some 204)) else d1614 (change p 182 (some 204))) = d4554 p
  rw [sub4819, sub4814]
  rfl
theorem sub4821 (p : Pattern) : d1620 (change p 182 (some 204)) = d4555 p := by
  change (if p 162 then d176 (change p 182 (some 204)) else d46 (change p 182 (some 204))) = d4555 p
  rw [sub4693, sub4652]
  rfl
theorem sub4822 (p : Pattern) : d1621 (change p 182 (some 204)) = d4556 p := by
  change (if p 161 then d177 (change p 182 (some 204)) else d1620 (change p 182 (some 204))) = d4556 p
  rw [sub4694, sub4821]
  rfl
theorem sub4823 (p : Pattern) : d8 (change p 182 (some 204)) = d8 p := by
  rfl
theorem sub4824 (p : Pattern) : d190 (change p 182 (some 204)) = d190 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d8 (change p 182 (some 204))) = d190 p
  rw [sub4639, sub4823]
  rfl
theorem sub4825 (p : Pattern) : d191 (change p 182 (some 204)) = d191 p := by
  change (if p 246 then d190 (change p 182 (some 204)) else d8 (change p 182 (some 204))) = d191 p
  rw [sub4824, sub4823]
  rfl
theorem sub4826 (p : Pattern) : d1622 (change p 182 (some 204)) = d191 p := by
  change d191 (change p 182 (some 204)) = d191 p
  exact sub4825 p
theorem sub4827 (p : Pattern) : d1623 (change p 182 (some 204)) = d4557 p := by
  change (if p 163 then d1622 (change p 182 (some 204)) else d43 (change p 182 (some 204))) = d4557 p
  rw [sub4826, sub4649]
  rfl
theorem sub4828 (p : Pattern) : d1624 (change p 182 (some 204)) = d4558 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d1623 (change p 182 (some 204))) = d4558 p
  rw [sub4639, sub4827]
  rfl
theorem sub4829 (p : Pattern) : d1625 (change p 182 (some 204)) = d4559 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1624 (change p 182 (some 204))) = d4559 p
  rw [sub4639, sub4828]
  rfl
theorem sub4830 (p : Pattern) : d1626 (change p 182 (some 204)) = d4560 p := by
  change (if p 160 then d1625 (change p 182 (some 204)) else d1621 (change p 182 (some 204))) = d4560 p
  rw [sub4829, sub4822]
  rfl
theorem sub4831 (p : Pattern) : d1627 (change p 182 (some 204)) = d4561 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d43 (change p 182 (some 204))) = d4561 p
  rw [sub4680, sub4649]
  rfl
theorem sub4832 (p : Pattern) : d1628 (change p 182 (some 204)) = d4562 p := by
  change (if p 162 then d1627 (change p 182 (some 204)) else d66 (change p 182 (some 204))) = d4562 p
  rw [sub4831, sub4668]
  rfl
theorem sub4833 (p : Pattern) : d1629 (change p 182 (some 204)) = d4563 p := by
  change (if p 161 then d184 (change p 182 (some 204)) else d1628 (change p 182 (some 204))) = d4563 p
  rw [sub4698, sub4832]
  rfl
theorem sub4834 (p : Pattern) : d1630 (change p 182 (some 204)) = d4564 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d1622 (change p 182 (some 204))) = d4564 p
  rw [sub4639, sub4826]
  rfl
theorem sub4835 (p : Pattern) : d1631 (change p 182 (some 204)) = d4565 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d1630 (change p 182 (some 204))) = d4565 p
  rw [sub4639, sub4834]
  rfl
theorem sub4836 (p : Pattern) : d1632 (change p 182 (some 204)) = d4566 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1631 (change p 182 (some 204))) = d4566 p
  rw [sub4639, sub4835]
  rfl
theorem sub4837 (p : Pattern) : d1633 (change p 182 (some 204)) = d4567 p := by
  change (if p 160 then d1632 (change p 182 (some 204)) else d1629 (change p 182 (some 204))) = d4567 p
  rw [sub4836, sub4833]
  rfl
theorem sub4838 (p : Pattern) : d1634 (change p 182 (some 204)) = d4568 p := by
  change (if p 141 then d1633 (change p 182 (some 204)) else d1626 (change p 182 (some 204))) = d4568 p
  rw [sub4837, sub4830]
  rfl
theorem sub4839 (p : Pattern) : d1635 (change p 182 (some 204)) = d4569 p := by
  change (if p 138 then d1634 (change p 182 (some 204)) else d1619 (change p 182 (some 204))) = d4569 p
  rw [sub4838, sub4820]
  rfl
theorem sub4840 (p : Pattern) : d1636 (change p 182 (some 204)) = d4570 p := by
  change (if p 138 then d12 (change p 182 (some 204)) else d1634 (change p 182 (some 204))) = d4570 p
  rw [sub4639, sub4838]
  rfl
theorem sub4841 (p : Pattern) : d1637 (change p 182 (some 204)) = d4571 p := by
  change (if p 116 then d1636 (change p 182 (some 204)) else d1635 (change p 182 (some 204))) = d4571 p
  rw [sub4840, sub4839]
  rfl
theorem sub4842 (p : Pattern) : d1638 (change p 182 (some 204)) = d4572 p := by
  change (if p 115 then d1637 (change p 182 (some 204)) else d1565 (change p 182 (some 204))) = d4572 p
  rw [sub4841, sub4739]
  rfl
theorem sub4843 (p : Pattern) : d1639 (change p 182 (some 204)) = d4573 p := by
  change (if p 71 then d1638 (change p 182 (some 204)) else d1552 (change p 182 (some 204))) = d4573 p
  rw [sub4842, sub4726]
  rfl
theorem sub4844 (p : Pattern) : d215 (change p 182 (some 204)) = d4574 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d125 (change p 182 (some 204))) = d4574 p
  rw [sub4639, sub4756]
  rfl
theorem sub4845 (p : Pattern) : d1640 (change p 182 (some 204)) = d4575 p := by
  change (if p 162 then d215 (change p 182 (some 204)) else d1581 (change p 182 (some 204))) = d4575 p
  rw [sub4844, sub4770]
  rfl
theorem sub4846 (p : Pattern) : d217 (change p 182 (some 204)) = d4576 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d215 (change p 182 (some 204))) = d4576 p
  rw [sub4639, sub4844]
  rfl
theorem sub4847 (p : Pattern) : d1641 (change p 182 (some 204)) = d4577 p := by
  change (if p 161 then d217 (change p 182 (some 204)) else d1640 (change p 182 (some 204))) = d4577 p
  rw [sub4846, sub4845]
  rfl
theorem sub4848 (p : Pattern) : d1642 (change p 182 (some 204)) = d4575 p := by
  change (if p 162 then d215 (change p 182 (some 204)) else d1584 (change p 182 (some 204))) = d4575 p
  rw [sub4844, sub4776]
  rfl
theorem sub4849 (p : Pattern) : d1643 (change p 182 (some 204)) = d4577 p := by
  change (if p 161 then d217 (change p 182 (some 204)) else d1642 (change p 182 (some 204))) = d4577 p
  rw [sub4846, sub4848]
  rfl
theorem sub4850 (p : Pattern) : d1644 (change p 182 (some 204)) = d4577 p := by
  change (if p 160 then d1643 (change p 182 (some 204)) else d1641 (change p 182 (some 204))) = d4577 p
  rw [sub4849, sub4847]
  simp only [ite_self]
theorem sub4851 (p : Pattern) : d1645 (change p 182 (some 204)) = d4578 p := by
  change (if p 141 then d1644 (change p 182 (some 204)) else d1579 (change p 182 (some 204))) = d4578 p
  rw [sub4850, sub4764]
  rfl
theorem sub4852 (p : Pattern) : d1646 (change p 182 (some 204)) = d4579 p := by
  change (if p 160 then d1591 (change p 182 (some 204)) else d1643 (change p 182 (some 204))) = d4579 p
  rw [sub4791, sub4849]
  rfl
theorem sub4853 (p : Pattern) : d1647 (change p 182 (some 204)) = d4580 p := by
  change (if p 141 then d1646 (change p 182 (some 204)) else d1590 (change p 182 (some 204))) = d4580 p
  rw [sub4852, sub4788]
  rfl
theorem sub4854 (p : Pattern) : d1648 (change p 182 (some 204)) = d4581 p := by
  change (if p 138 then d1647 (change p 182 (some 204)) else d1645 (change p 182 (some 204))) = d4581 p
  rw [sub4853, sub4851]
  rfl
theorem sub4855 (p : Pattern) : d1649 (change p 182 (some 204)) = d4582 p := by
  change (if p 138 then d1598 (change p 182 (some 204)) else d1647 (change p 182 (some 204))) = d4582 p
  rw [sub4798, sub4853]
  rfl
theorem sub4856 (p : Pattern) : d1650 (change p 182 (some 204)) = d4583 p := by
  change (if p 116 then d1649 (change p 182 (some 204)) else d1648 (change p 182 (some 204))) = d4583 p
  rw [sub4855, sub4854]
  rfl
theorem sub4857 (p : Pattern) : d1651 (change p 182 (some 204)) = d4584 p := by
  change (if p 162 then d215 (change p 182 (some 204)) else d139 (change p 182 (some 204))) = d4584 p
  rw [sub4844, sub4769]
  rfl
theorem sub4858 (p : Pattern) : d1652 (change p 182 (some 204)) = d4585 p := by
  change (if p 161 then d231 (change p 182 (some 204)) else d1651 (change p 182 (some 204))) = d4585 p
  rw [sub4790, sub4857]
  rfl
theorem sub4859 (p : Pattern) : d1653 (change p 182 (some 204)) = d4586 p := by
  change (if p 160 then d1652 (change p 182 (some 204)) else d1603 (change p 182 (some 204))) = d4586 p
  rw [sub4858, sub4803]
  rfl
theorem sub4860 (p : Pattern) : d1654 (change p 182 (some 204)) = d4587 p := by
  change (if p 162 then d230 (change p 182 (some 204)) else d125 (change p 182 (some 204))) = d4587 p
  rw [sub4789, sub4756]
  rfl
theorem sub4861 (p : Pattern) : d237 (change p 182 (some 204)) = d4588 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d49 (change p 182 (some 204))) = d4588 p
  rw [sub4639, sub4658]
  rfl
theorem sub4862 (p : Pattern) : d1655 (change p 182 (some 204)) = d4589 p := by
  change (if p 161 then d237 (change p 182 (some 204)) else d1654 (change p 182 (some 204))) = d4589 p
  rw [sub4861, sub4860]
  rfl
theorem sub4863 (p : Pattern) : d1656 (change p 182 (some 204)) = d4590 p := by
  change (if p 160 then d1655 (change p 182 (some 204)) else d1643 (change p 182 (some 204))) = d4590 p
  rw [sub4862, sub4849]
  rfl
theorem sub4864 (p : Pattern) : d1657 (change p 182 (some 204)) = d4591 p := by
  change (if p 141 then d1656 (change p 182 (some 204)) else d1653 (change p 182 (some 204))) = d4591 p
  rw [sub4863, sub4859]
  rfl
theorem sub4865 (p : Pattern) : d1658 (change p 182 (some 204)) = d4592 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d139 (change p 182 (some 204))) = d4592 p
  rw [sub4680, sub4769]
  rfl
theorem sub4866 (p : Pattern) : d1659 (change p 182 (some 204)) = d4593 p := by
  change (if p 162 then d1658 (change p 182 (some 204)) else d124 (change p 182 (some 204))) = d4593 p
  rw [sub4865, sub4752]
  rfl
theorem sub4867 (p : Pattern) : d1660 (change p 182 (some 204)) = d4594 p := by
  change (if p 161 then d144 (change p 182 (some 204)) else d1659 (change p 182 (some 204))) = d4594 p
  rw [sub4774, sub4866]
  rfl
theorem sub4868 (p : Pattern) : d1661 (change p 182 (some 204)) = d4595 p := by
  change (if p 160 then d1591 (change p 182 (some 204)) else d1660 (change p 182 (some 204))) = d4595 p
  rw [sub4791, sub4867]
  rfl
theorem sub4869 (p : Pattern) : d1662 (change p 182 (some 204)) = d4596 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d237 (change p 182 (some 204))) = d4596 p
  rw [sub4639, sub4861]
  rfl
theorem sub4870 (p : Pattern) : d1663 (change p 182 (some 204)) = d4597 p := by
  change (if p 160 then d1662 (change p 182 (some 204)) else d1652 (change p 182 (some 204))) = d4597 p
  rw [sub4869, sub4858]
  rfl
theorem sub4871 (p : Pattern) : d1664 (change p 182 (some 204)) = d4598 p := by
  change (if p 141 then d1663 (change p 182 (some 204)) else d1661 (change p 182 (some 204))) = d4598 p
  rw [sub4870, sub4868]
  rfl
theorem sub4872 (p : Pattern) : d1665 (change p 182 (some 204)) = d4599 p := by
  change (if p 138 then d1664 (change p 182 (some 204)) else d1657 (change p 182 (some 204))) = d4599 p
  rw [sub4871, sub4864]
  rfl
theorem sub4873 (p : Pattern) : d1666 (change p 182 (some 204)) = d4600 p := by
  change (if p 163 then d48 (change p 182 (some 204)) else d139 (change p 182 (some 204))) = d4600 p
  rw [sub4657, sub4769]
  rfl
theorem sub4874 (p : Pattern) : d1667 (change p 182 (some 204)) = d4601 p := by
  change (if p 162 then d1666 (change p 182 (some 204)) else d124 (change p 182 (some 204))) = d4601 p
  rw [sub4873, sub4752]
  rfl
theorem sub4875 (p : Pattern) : d1668 (change p 182 (some 204)) = d4602 p := by
  change (if p 163 then d48 (change p 182 (some 204)) else d125 (change p 182 (some 204))) = d4602 p
  rw [sub4657, sub4756]
  rfl
theorem sub4876 (p : Pattern) : d1669 (change p 182 (some 204)) = d4603 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d1668 (change p 182 (some 204))) = d4603 p
  rw [sub4639, sub4875]
  rfl
theorem sub4877 (p : Pattern) : d1670 (change p 182 (some 204)) = d4604 p := by
  change (if p 161 then d1669 (change p 182 (some 204)) else d1667 (change p 182 (some 204))) = d4604 p
  rw [sub4876, sub4874]
  rfl
theorem sub4878 (p : Pattern) : d1671 (change p 182 (some 204)) = d4605 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d229 (change p 182 (some 204))) = d4605 p
  rw [sub4680, sub4784]
  rfl
theorem sub4879 (p : Pattern) : d1672 (change p 182 (some 204)) = d4606 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d1671 (change p 182 (some 204))) = d4606 p
  rw [sub4639, sub4878]
  rfl
theorem sub4880 (p : Pattern) : d1673 (change p 182 (some 204)) = d4607 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1672 (change p 182 (some 204))) = d4607 p
  rw [sub4639, sub4879]
  rfl
theorem sub4881 (p : Pattern) : d1674 (change p 182 (some 204)) = d4608 p := by
  change (if p 160 then d1673 (change p 182 (some 204)) else d1670 (change p 182 (some 204))) = d4608 p
  rw [sub4880, sub4877]
  rfl
theorem sub4882 (p : Pattern) : d1675 (change p 182 (some 204)) = d4609 p := by
  change (if p 141 then d1663 (change p 182 (some 204)) else d1674 (change p 182 (some 204))) = d4609 p
  rw [sub4870, sub4881]
  rfl
theorem sub4883 (p : Pattern) : d1676 (change p 182 (some 204)) = d4610 p := by
  change (if p 138 then d12 (change p 182 (some 204)) else d1675 (change p 182 (some 204))) = d4610 p
  rw [sub4639, sub4882]
  rfl
theorem sub4884 (p : Pattern) : d1677 (change p 182 (some 204)) = d4611 p := by
  change (if p 116 then d1676 (change p 182 (some 204)) else d1665 (change p 182 (some 204))) = d4611 p
  rw [sub4883, sub4872]
  rfl
theorem sub4885 (p : Pattern) : d1678 (change p 182 (some 204)) = d4612 p := by
  change (if p 115 then d1677 (change p 182 (some 204)) else d1650 (change p 182 (some 204))) = d4612 p
  rw [sub4884, sub4856]
  rfl
theorem sub4886 (p : Pattern) : d1679 (change p 182 (some 204)) = d4613 p := by
  change (if p 71 then d1678 (change p 182 (some 204)) else d1552 (change p 182 (some 204))) = d4613 p
  rw [sub4885, sub4726]
  rfl
theorem sub4887 (p : Pattern) : d1680 (change p 182 (some 204)) = d4614 p := by
  change (if p 49 then d1679 (change p 182 (some 204)) else d1639 (change p 182 (some 204))) = d4614 p
  rw [sub4886, sub4843]
  rfl
theorem sub4888 (p : Pattern) : d1681 (change p 182 (some 204)) = d4615 p := by
  change (if p 48 then d1680 (change p 182 (some 204)) else d1611 (change p 182 (some 204))) = d4615 p
  rw [sub4887, sub4811]
  rfl
theorem sub4889 (p : Pattern) : d0 (change p 161 (some 162)) = d0 p := by
  rfl
theorem sub4890 (p : Pattern) : d12 (change p 161 (some 162)) = d12 p := by
  rfl
theorem sub4891 (p : Pattern) : d13 (change p 161 (some 162)) = d13 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d0 (change p 161 (some 162))) = d13 p
  rw [sub4890, sub4889]
  rfl
theorem sub4892 (p : Pattern) : d14 (change p 161 (some 162)) = d14 p := by
  change (if p 246 then d13 (change p 161 (some 162)) else d0 (change p 161 (some 162))) = d14 p
  rw [sub4891, sub4889]
  rfl
theorem sub4893 (p : Pattern) : d15 (change p 161 (some 162)) = d15 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d14 (change p 161 (some 162))) = d15 p
  rw [sub4890, sub4892]
  rfl
theorem sub4894 (p : Pattern) : d16 (change p 161 (some 162)) = d16 p := by
  change (if p 182 then d15 (change p 161 (some 162)) else d14 (change p 161 (some 162))) = d16 p
  rw [sub4893, sub4892]
  rfl
theorem sub4895 (p : Pattern) : d4 (change p 161 (some 162)) = d4 p := by
  rfl
theorem sub4896 (p : Pattern) : d17 (change p 161 (some 162)) = d17 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d4 (change p 161 (some 162))) = d17 p
  rw [sub4890, sub4895]
  rfl
theorem sub4897 (p : Pattern) : d18 (change p 161 (some 162)) = d18 p := by
  change (if p 246 then d17 (change p 161 (some 162)) else d4 (change p 161 (some 162))) = d18 p
  rw [sub4896, sub4895]
  rfl
theorem sub4898 (p : Pattern) : d19 (change p 161 (some 162)) = d19 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d18 (change p 161 (some 162))) = d19 p
  rw [sub4890, sub4897]
  rfl
theorem sub4899 (p : Pattern) : d20 (change p 161 (some 162)) = d20 p := by
  change (if p 182 then d19 (change p 161 (some 162)) else d18 (change p 161 (some 162))) = d20 p
  rw [sub4898, sub4897]
  rfl
theorem sub4900 (p : Pattern) : d21 (change p 161 (some 162)) = d21 p := by
  change (if p 163 then d20 (change p 161 (some 162)) else d16 (change p 161 (some 162))) = d21 p
  rw [sub4899, sub4894]
  rfl
theorem sub4901 (p : Pattern) : d22 (change p 161 (some 162)) = d21 p := by
  change d21 (change p 161 (some 162)) = d21 p
  exact sub4900 p
theorem sub4902 (p : Pattern) : d790 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4903 (p : Pattern) : d2 (change p 161 (some 162)) = d2 p := by
  rfl
theorem sub4904 (p : Pattern) : d30 (change p 161 (some 162)) = d30 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d2 (change p 161 (some 162))) = d30 p
  rw [sub4890, sub4903]
  rfl
theorem sub4905 (p : Pattern) : d31 (change p 161 (some 162)) = d31 p := by
  change (if p 246 then d30 (change p 161 (some 162)) else d2 (change p 161 (some 162))) = d31 p
  rw [sub4904, sub4903]
  rfl
theorem sub4906 (p : Pattern) : d32 (change p 161 (some 162)) = d32 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d31 (change p 161 (some 162))) = d32 p
  rw [sub4890, sub4905]
  rfl
theorem sub4907 (p : Pattern) : d53 (change p 161 (some 162)) = d53 p := by
  change (if p 182 then d32 (change p 161 (some 162)) else d31 (change p 161 (some 162))) = d53 p
  rw [sub4906, sub4905]
  rfl
theorem sub4908 (p : Pattern) : d6 (change p 161 (some 162)) = d6 p := by
  rfl
theorem sub4909 (p : Pattern) : d34 (change p 161 (some 162)) = d34 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d6 (change p 161 (some 162))) = d34 p
  rw [sub4890, sub4908]
  rfl
theorem sub4910 (p : Pattern) : d35 (change p 161 (some 162)) = d35 p := by
  change (if p 246 then d34 (change p 161 (some 162)) else d6 (change p 161 (some 162))) = d35 p
  rw [sub4909, sub4908]
  rfl
theorem sub4911 (p : Pattern) : d36 (change p 161 (some 162)) = d36 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d35 (change p 161 (some 162))) = d36 p
  rw [sub4890, sub4910]
  rfl
theorem sub4912 (p : Pattern) : d78 (change p 161 (some 162)) = d78 p := by
  change (if p 182 then d36 (change p 161 (some 162)) else d35 (change p 161 (some 162))) = d78 p
  rw [sub4911, sub4910]
  rfl
theorem sub4913 (p : Pattern) : d79 (change p 161 (some 162)) = d79 p := by
  change (if p 163 then d78 (change p 161 (some 162)) else d53 (change p 161 (some 162))) = d79 p
  rw [sub4912, sub4907]
  rfl
theorem sub4914 (p : Pattern) : d791 (change p 161 (some 162)) = d79 p := by
  change d79 (change p 161 (some 162)) = d79 p
  exact sub4913 p
theorem sub4915 (p : Pattern) : d792 (change p 161 (some 162)) = d79 p := by
  change d791 (change p 161 (some 162)) = d79 p
  exact sub4914 p
theorem sub4916 (p : Pattern) : d793 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d792 (change p 161 (some 162)) else d790 (change p 161 (some 162))) = d4619 p
  rw [sub4915, sub4902]
  rfl
theorem sub4917 (p : Pattern) : d9 (change p 161 (some 162)) = d9 p := by
  rfl
theorem sub4918 (p : Pattern) : d23 (change p 161 (some 162)) = d23 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d9 (change p 161 (some 162))) = d23 p
  rw [sub4890, sub4917]
  rfl
theorem sub4919 (p : Pattern) : d24 (change p 161 (some 162)) = d24 p := by
  change (if p 246 then d23 (change p 161 (some 162)) else d9 (change p 161 (some 162))) = d24 p
  rw [sub4918, sub4917]
  rfl
end NetHack.Sokoban22Refined85
