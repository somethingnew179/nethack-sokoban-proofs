/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions38
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4680 (p : Pattern) : d72 (change p 182 (some 204)) = d40 p := by
  change d40 (change p 182 (some 204)) = d40 p
  exact sub4679 p
theorem sub4681 (p : Pattern) : d73 (change p 182 (some 204)) = d4486 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d72 (change p 182 (some 204))) = d4486 p
  rw [sub4639, sub4680]
  rfl
theorem sub4682 (p : Pattern) : d74 (change p 182 (some 204)) = d4487 p := by
  change (if p 162 then d73 (change p 182 (some 204)) else d71 (change p 182 (some 204))) = d4487 p
  rw [sub4681, sub4676]
  rfl
theorem sub4683 (p : Pattern) : d1517 (change p 182 (some 204)) = d4488 p := by
  change (if p 161 then d74 (change p 182 (some 204)) else d1516 (change p 182 (some 204))) = d4488 p
  rw [sub4682, sub4671]
  rfl
theorem sub4684 (p : Pattern) : d1518 (change p 182 (some 204)) = d4482 p := by
  change (if p 163 then d66 (change p 182 (some 204)) else d46 (change p 182 (some 204))) = d4482 p
  rw [sub4668, sub4652]
  rfl
theorem sub4685 (p : Pattern) : d1519 (change p 182 (some 204)) = d4484 p := by
  change (if p 162 then d68 (change p 182 (some 204)) else d1518 (change p 182 (some 204))) = d4484 p
  rw [sub4670, sub4684]
  rfl
theorem sub4686 (p : Pattern) : d1520 (change p 182 (some 204)) = d4488 p := by
  change (if p 161 then d74 (change p 182 (some 204)) else d1519 (change p 182 (some 204))) = d4488 p
  rw [sub4682, sub4685]
  rfl
theorem sub4687 (p : Pattern) : d1521 (change p 182 (some 204)) = d4488 p := by
  change (if p 160 then d1520 (change p 182 (some 204)) else d1517 (change p 182 (some 204))) = d4488 p
  rw [sub4686, sub4683]
  simp only [ite_self]
theorem sub4688 (p : Pattern) : d1522 (change p 182 (some 204)) = d4489 p := by
  change (if p 141 then d1521 (change p 182 (some 204)) else d1513 (change p 182 (some 204))) = d4489 p
  rw [sub4687, sub4663]
  rfl
theorem sub4689 (p : Pattern) : d6 (change p 182 (some 204)) = d6 p := by
  rfl
theorem sub4690 (p : Pattern) : d34 (change p 182 (some 204)) = d34 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d6 (change p 182 (some 204))) = d34 p
  rw [sub4639, sub4689]
  rfl
theorem sub4691 (p : Pattern) : d35 (change p 182 (some 204)) = d35 p := by
  change (if p 246 then d34 (change p 182 (some 204)) else d6 (change p 182 (some 204))) = d35 p
  rw [sub4690, sub4689]
  rfl
theorem sub4692 (p : Pattern) : d173 (change p 182 (some 204)) = d35 p := by
  change d35 (change p 182 (some 204)) = d35 p
  exact sub4691 p
theorem sub4693 (p : Pattern) : d176 (change p 182 (some 204)) = d4490 p := by
  change (if p 163 then d173 (change p 182 (some 204)) else d66 (change p 182 (some 204))) = d4490 p
  rw [sub4692, sub4668]
  rfl
theorem sub4694 (p : Pattern) : d177 (change p 182 (some 204)) = d4491 p := by
  change (if p 162 then d73 (change p 182 (some 204)) else d176 (change p 182 (some 204))) = d4491 p
  rw [sub4681, sub4693]
  rfl
theorem sub4695 (p : Pattern) : d1523 (change p 182 (some 204)) = d4492 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d177 (change p 182 (some 204))) = d4492 p
  rw [sub4639, sub4694]
  rfl
theorem sub4696 (p : Pattern) : d1524 (change p 182 (some 204)) = d4493 p := by
  change (if p 160 then d1523 (change p 182 (some 204)) else d1512 (change p 182 (some 204))) = d4493 p
  rw [sub4695, sub4662]
  rfl
theorem sub4697 (p : Pattern) : d183 (change p 182 (some 204)) = d4494 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d173 (change p 182 (some 204))) = d4494 p
  rw [sub4639, sub4692]
  rfl
theorem sub4698 (p : Pattern) : d184 (change p 182 (some 204)) = d4495 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d183 (change p 182 (some 204))) = d4495 p
  rw [sub4639, sub4697]
  rfl
theorem sub4699 (p : Pattern) : d1525 (change p 182 (some 204)) = d4496 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d184 (change p 182 (some 204))) = d4496 p
  rw [sub4639, sub4698]
  rfl
theorem sub4700 (p : Pattern) : d1526 (change p 182 (some 204)) = d4497 p := by
  change (if p 160 then d1525 (change p 182 (some 204)) else d1520 (change p 182 (some 204))) = d4497 p
  rw [sub4699, sub4686]
  rfl
theorem sub4701 (p : Pattern) : d1527 (change p 182 (some 204)) = d4498 p := by
  change (if p 141 then d1526 (change p 182 (some 204)) else d1524 (change p 182 (some 204))) = d4498 p
  rw [sub4700, sub4696]
  rfl
theorem sub4702 (p : Pattern) : d1528 (change p 182 (some 204)) = d4499 p := by
  change (if p 138 then d1527 (change p 182 (some 204)) else d1522 (change p 182 (some 204))) = d4499 p
  rw [sub4701, sub4688]
  rfl
theorem sub4703 (p : Pattern) : d1529 (change p 182 (some 204)) = d14 p := by
  change (if p 163 then d46 (change p 182 (some 204)) else d1507 (change p 182 (some 204))) = d14 p
  rw [sub4652, sub4645]
  simp only [ite_self]
theorem sub4704 (p : Pattern) : d1530 (change p 182 (some 204)) = d4478 p := by
  change (if p 162 then d47 (change p 182 (some 204)) else d1529 (change p 182 (some 204))) = d4478 p
  rw [sub4653, sub4703]
  rfl
theorem sub4705 (p : Pattern) : d1531 (change p 182 (some 204)) = d4481 p := by
  change (if p 161 then d50 (change p 182 (some 204)) else d1530 (change p 182 (some 204))) = d4481 p
  rw [sub4659, sub4704]
  rfl
theorem sub4706 (p : Pattern) : d1532 (change p 182 (some 204)) = d4493 p := by
  change (if p 160 then d1523 (change p 182 (some 204)) else d1531 (change p 182 (some 204))) = d4493 p
  rw [sub4695, sub4705]
  rfl
theorem sub4707 (p : Pattern) : d1533 (change p 182 (some 204)) = d4498 p := by
  change (if p 141 then d1526 (change p 182 (some 204)) else d1532 (change p 182 (some 204))) = d4498 p
  rw [sub4700, sub4706]
  rfl
theorem sub4708 (p : Pattern) : d1534 (change p 182 (some 204)) = d4500 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d48 (change p 182 (some 204))) = d4500 p
  rw [sub4680, sub4657]
  rfl
theorem sub4709 (p : Pattern) : d1535 (change p 182 (some 204)) = d4501 p := by
  change (if p 162 then d73 (change p 182 (some 204)) else d1534 (change p 182 (some 204))) = d4501 p
  rw [sub4681, sub4708]
  rfl
theorem sub4710 (p : Pattern) : d1536 (change p 182 (some 204)) = d4502 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d73 (change p 182 (some 204))) = d4502 p
  rw [sub4639, sub4681]
  rfl
theorem sub4711 (p : Pattern) : d1537 (change p 182 (some 204)) = d4503 p := by
  change (if p 161 then d1536 (change p 182 (some 204)) else d1535 (change p 182 (some 204))) = d4503 p
  rw [sub4710, sub4709]
  rfl
theorem sub4712 (p : Pattern) : d1538 (change p 182 (some 204)) = d4504 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1536 (change p 182 (some 204))) = d4504 p
  rw [sub4639, sub4710]
  rfl
theorem sub4713 (p : Pattern) : d1539 (change p 182 (some 204)) = d4505 p := by
  change (if p 160 then d1538 (change p 182 (some 204)) else d1537 (change p 182 (some 204))) = d4505 p
  rw [sub4712, sub4711]
  rfl
theorem sub4714 (p : Pattern) : d1540 (change p 182 (some 204)) = d4506 p := by
  change (if p 160 then d12 (change p 182 (some 204)) else d1538 (change p 182 (some 204))) = d4506 p
  rw [sub4639, sub4712]
  rfl
theorem sub4715 (p : Pattern) : d1541 (change p 182 (some 204)) = d4507 p := by
  change (if p 141 then d1540 (change p 182 (some 204)) else d1539 (change p 182 (some 204))) = d4507 p
  rw [sub4714, sub4713]
  rfl
theorem sub4716 (p : Pattern) : d1542 (change p 182 (some 204)) = d4508 p := by
  change (if p 138 then d1541 (change p 182 (some 204)) else d1533 (change p 182 (some 204))) = d4508 p
  rw [sub4715, sub4707]
  rfl
theorem sub4717 (p : Pattern) : d1543 (change p 182 (some 204)) = d4509 p := by
  change (if p 116 then d1542 (change p 182 (some 204)) else d1528 (change p 182 (some 204))) = d4509 p
  rw [sub4716, sub4702]
  rfl
theorem sub4718 (p : Pattern) : d1544 (change p 182 (some 204)) = d14 p := by
  change (if p 163 then d46 (change p 182 (some 204)) else d1505 (change p 182 (some 204))) = d14 p
  rw [sub4652, sub4643]
  simp only [ite_self]
theorem sub4719 (p : Pattern) : d1545 (change p 182 (some 204)) = d4478 p := by
  change (if p 162 then d47 (change p 182 (some 204)) else d1544 (change p 182 (some 204))) = d4478 p
  rw [sub4653, sub4718]
  rfl
theorem sub4720 (p : Pattern) : d1546 (change p 182 (some 204)) = d4481 p := by
  change (if p 161 then d50 (change p 182 (some 204)) else d1545 (change p 182 (some 204))) = d4481 p
  rw [sub4659, sub4719]
  rfl
theorem sub4721 (p : Pattern) : d1547 (change p 182 (some 204)) = d4481 p := by
  change (if p 160 then d1512 (change p 182 (some 204)) else d1546 (change p 182 (some 204))) = d4481 p
  rw [sub4662, sub4720]
  simp only [ite_self]
theorem sub4722 (p : Pattern) : d1548 (change p 182 (some 204)) = d4489 p := by
  change (if p 141 then d1520 (change p 182 (some 204)) else d1547 (change p 182 (some 204))) = d4489 p
  rw [sub4686, sub4721]
  rfl
theorem sub4723 (p : Pattern) : d1549 (change p 182 (some 204)) = d4499 p := by
  change (if p 138 then d1527 (change p 182 (some 204)) else d1548 (change p 182 (some 204))) = d4499 p
  rw [sub4701, sub4722]
  rfl
theorem sub4724 (p : Pattern) : d1550 (change p 182 (some 204)) = d4510 p := by
  change (if p 138 then d12 (change p 182 (some 204)) else d1527 (change p 182 (some 204))) = d4510 p
  rw [sub4639, sub4701]
  rfl
theorem sub4725 (p : Pattern) : d1551 (change p 182 (some 204)) = d4511 p := by
  change (if p 116 then d1550 (change p 182 (some 204)) else d1549 (change p 182 (some 204))) = d4511 p
  rw [sub4724, sub4723]
  rfl
theorem sub4726 (p : Pattern) : d1552 (change p 182 (some 204)) = d4512 p := by
  change (if p 115 then d1551 (change p 182 (some 204)) else d1543 (change p 182 (some 204))) = d4512 p
  rw [sub4725, sub4717]
  rfl
theorem sub4727 (p : Pattern) : d1553 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4728 (p : Pattern) : d1554 (change p 182 (some 204)) = d14 p := by
  change (if p 163 then d1507 (change p 182 (some 204)) else d1553 (change p 182 (some 204))) = d14 p
  rw [sub4645, sub4727]
  simp only [ite_self]
theorem sub4729 (p : Pattern) : d1555 (change p 182 (some 204)) = d4478 p := by
  change (if p 162 then d47 (change p 182 (some 204)) else d1554 (change p 182 (some 204))) = d4478 p
  rw [sub4653, sub4728]
  rfl
theorem sub4730 (p : Pattern) : d1556 (change p 182 (some 204)) = d4481 p := by
  change (if p 161 then d50 (change p 182 (some 204)) else d1555 (change p 182 (some 204))) = d4481 p
  rw [sub4659, sub4729]
  rfl
theorem sub4731 (p : Pattern) : d1557 (change p 182 (some 204)) = d4481 p := by
  change (if p 160 then d1512 (change p 182 (some 204)) else d1556 (change p 182 (some 204))) = d4481 p
  rw [sub4662, sub4730]
  simp only [ite_self]
theorem sub4732 (p : Pattern) : d1558 (change p 182 (some 204)) = d4482 p := by
  change (if p 163 then d66 (change p 182 (some 204)) else d1505 (change p 182 (some 204))) = d4482 p
  rw [sub4668, sub4643]
  rfl
theorem sub4733 (p : Pattern) : d1559 (change p 182 (some 204)) = d4484 p := by
  change (if p 162 then d68 (change p 182 (some 204)) else d1558 (change p 182 (some 204))) = d4484 p
  rw [sub4670, sub4732]
  rfl
theorem sub4734 (p : Pattern) : d1560 (change p 182 (some 204)) = d4488 p := by
  change (if p 161 then d74 (change p 182 (some 204)) else d1559 (change p 182 (some 204))) = d4488 p
  rw [sub4682, sub4733]
  rfl
theorem sub4735 (p : Pattern) : d1561 (change p 182 (some 204)) = d4488 p := by
  change (if p 160 then d1520 (change p 182 (some 204)) else d1560 (change p 182 (some 204))) = d4488 p
  rw [sub4686, sub4734]
  simp only [ite_self]
theorem sub4736 (p : Pattern) : d1562 (change p 182 (some 204)) = d4489 p := by
  change (if p 141 then d1561 (change p 182 (some 204)) else d1557 (change p 182 (some 204))) = d4489 p
  rw [sub4735, sub4731]
  rfl
theorem sub4737 (p : Pattern) : d1563 (change p 182 (some 204)) = d4499 p := by
  change (if p 138 then d1527 (change p 182 (some 204)) else d1562 (change p 182 (some 204))) = d4499 p
  rw [sub4701, sub4736]
  rfl
theorem sub4738 (p : Pattern) : d1564 (change p 182 (some 204)) = d4508 p := by
  change (if p 138 then d1541 (change p 182 (some 204)) else d1527 (change p 182 (some 204))) = d4508 p
  rw [sub4715, sub4701]
  rfl
theorem sub4739 (p : Pattern) : d1565 (change p 182 (some 204)) = d4509 p := by
  change (if p 116 then d1564 (change p 182 (some 204)) else d1563 (change p 182 (some 204))) = d4509 p
  rw [sub4738, sub4737]
  rfl
theorem sub4740 (p : Pattern) : d1566 (change p 182 (some 204)) = d4481 p := by
  change (if p 160 then d1512 (change p 182 (some 204)) else d1531 (change p 182 (some 204))) = d4481 p
  rw [sub4662, sub4705]
  simp only [ite_self]
theorem sub4741 (p : Pattern) : d1567 (change p 182 (some 204)) = d4489 p := by
  change (if p 141 then d1520 (change p 182 (some 204)) else d1566 (change p 182 (some 204))) = d4489 p
  rw [sub4686, sub4740]
  rfl
theorem sub4742 (p : Pattern) : d1568 (change p 182 (some 204)) = d4499 p := by
  change (if p 138 then d1527 (change p 182 (some 204)) else d1567 (change p 182 (some 204))) = d4499 p
  rw [sub4701, sub4741]
  rfl
theorem sub4743 (p : Pattern) : d1569 (change p 182 (some 204)) = d4511 p := by
  change (if p 116 then d1550 (change p 182 (some 204)) else d1568 (change p 182 (some 204))) = d4511 p
  rw [sub4724, sub4742]
  rfl
theorem sub4744 (p : Pattern) : d1570 (change p 182 (some 204)) = d4512 p := by
  change (if p 115 then d1569 (change p 182 (some 204)) else d1565 (change p 182 (some 204))) = d4512 p
  rw [sub4743, sub4739]
  rfl
theorem sub4745 (p : Pattern) : d1571 (change p 182 (some 204)) = d4512 p := by
  change (if p 71 then d1570 (change p 182 (some 204)) else d1552 (change p 182 (some 204))) = d4512 p
  rw [sub4744, sub4726]
  simp only [ite_self]
theorem sub4746 (p : Pattern) : d1 (change p 182 (some 204)) = d1 p := by
  rfl
theorem sub4747 (p : Pattern) : d102 (change p 182 (some 204)) = d102 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d1 (change p 182 (some 204))) = d102 p
  rw [sub4639, sub4746]
  rfl
theorem sub4748 (p : Pattern) : d103 (change p 182 (some 204)) = d103 p := by
  change (if p 246 then d102 (change p 182 (some 204)) else d1 (change p 182 (some 204))) = d103 p
  rw [sub4747, sub4746]
  rfl
theorem sub4749 (p : Pattern) : d1572 (change p 182 (some 204)) = d103 p := by
  change d103 (change p 182 (some 204)) = d103 p
  exact sub4748 p
theorem sub4750 (p : Pattern) : d1573 (change p 182 (some 204)) = d103 p := by
  change d103 (change p 182 (some 204)) = d103 p
  exact sub4748 p
theorem sub4751 (p : Pattern) : d1574 (change p 182 (some 204)) = d103 p := by
  change (if p 163 then d1573 (change p 182 (some 204)) else d1572 (change p 182 (some 204))) = d103 p
  rw [sub4750, sub4749]
  simp only [ite_self]
theorem sub4752 (p : Pattern) : d124 (change p 182 (some 204)) = d103 p := by
  change d103 (change p 182 (some 204)) = d103 p
  exact sub4748 p
theorem sub4753 (p : Pattern) : d5 (change p 182 (some 204)) = d5 p := by
  rfl
theorem sub4754 (p : Pattern) : d106 (change p 182 (some 204)) = d106 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d5 (change p 182 (some 204))) = d106 p
  rw [sub4639, sub4753]
  rfl
theorem sub4755 (p : Pattern) : d107 (change p 182 (some 204)) = d107 p := by
  change (if p 246 then d106 (change p 182 (some 204)) else d5 (change p 182 (some 204))) = d107 p
  rw [sub4754, sub4753]
  rfl
theorem sub4756 (p : Pattern) : d125 (change p 182 (some 204)) = d107 p := by
  change d107 (change p 182 (some 204)) = d107 p
  exact sub4755 p
theorem sub4757 (p : Pattern) : d126 (change p 182 (some 204)) = d4513 p := by
  change (if p 163 then d125 (change p 182 (some 204)) else d124 (change p 182 (some 204))) = d4513 p
  rw [sub4756, sub4752]
  rfl
theorem sub4758 (p : Pattern) : d1575 (change p 182 (some 204)) = d4514 p := by
  change (if p 162 then d126 (change p 182 (some 204)) else d1574 (change p 182 (some 204))) = d4514 p
  rw [sub4757, sub4751]
  rfl
theorem sub4759 (p : Pattern) : d128 (change p 182 (some 204)) = d4515 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d70 (change p 182 (some 204))) = d4515 p
  rw [sub4639, sub4675]
  rfl
theorem sub4760 (p : Pattern) : d129 (change p 182 (some 204)) = d4516 p := by
  change (if p 162 then d128 (change p 182 (some 204)) else d126 (change p 182 (some 204))) = d4516 p
  rw [sub4759, sub4757]
  rfl
theorem sub4761 (p : Pattern) : d1576 (change p 182 (some 204)) = d4517 p := by
  change (if p 161 then d129 (change p 182 (some 204)) else d1575 (change p 182 (some 204))) = d4517 p
  rw [sub4760, sub4758]
  rfl
theorem sub4762 (p : Pattern) : d1577 (change p 182 (some 204)) = d4514 p := by
  change (if p 162 then d126 (change p 182 (some 204)) else d124 (change p 182 (some 204))) = d4514 p
  rw [sub4757, sub4752]
  rfl
theorem sub4763 (p : Pattern) : d1578 (change p 182 (some 204)) = d4517 p := by
  change (if p 161 then d129 (change p 182 (some 204)) else d1577 (change p 182 (some 204))) = d4517 p
  rw [sub4760, sub4762]
  rfl
theorem sub4764 (p : Pattern) : d1579 (change p 182 (some 204)) = d4517 p := by
  change (if p 160 then d1578 (change p 182 (some 204)) else d1576 (change p 182 (some 204))) = d4517 p
  rw [sub4763, sub4761]
  simp only [ite_self]
theorem sub4765 (p : Pattern) : d1580 (change p 182 (some 204)) = d103 p := by
  change d103 (change p 182 (some 204)) = d103 p
  exact sub4748 p
theorem sub4766 (p : Pattern) : d3 (change p 182 (some 204)) = d3 p := by
  rfl
theorem sub4767 (p : Pattern) : d115 (change p 182 (some 204)) = d115 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d3 (change p 182 (some 204))) = d115 p
  rw [sub4639, sub4766]
  rfl
theorem sub4768 (p : Pattern) : d116 (change p 182 (some 204)) = d116 p := by
  change (if p 246 then d115 (change p 182 (some 204)) else d3 (change p 182 (some 204))) = d116 p
  rw [sub4767, sub4766]
  rfl
theorem sub4769 (p : Pattern) : d139 (change p 182 (some 204)) = d116 p := by
  change d116 (change p 182 (some 204)) = d116 p
  exact sub4768 p
theorem sub4770 (p : Pattern) : d1581 (change p 182 (some 204)) = d4518 p := by
  change (if p 163 then d139 (change p 182 (some 204)) else d1580 (change p 182 (some 204))) = d4518 p
  rw [sub4769, sub4765]
  rfl
theorem sub4771 (p : Pattern) : d141 (change p 182 (some 204)) = d4519 p := by
  change (if p 163 then d70 (change p 182 (some 204)) else d125 (change p 182 (some 204))) = d4519 p
  rw [sub4675, sub4756]
  rfl
theorem sub4772 (p : Pattern) : d1582 (change p 182 (some 204)) = d4520 p := by
  change (if p 162 then d141 (change p 182 (some 204)) else d1581 (change p 182 (some 204))) = d4520 p
  rw [sub4771, sub4770]
  rfl
theorem sub4773 (p : Pattern) : d143 (change p 182 (some 204)) = d4521 p := by
  change (if p 163 then d72 (change p 182 (some 204)) else d125 (change p 182 (some 204))) = d4521 p
  rw [sub4680, sub4756]
  rfl
theorem sub4774 (p : Pattern) : d144 (change p 182 (some 204)) = d4522 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d143 (change p 182 (some 204))) = d4522 p
  rw [sub4639, sub4773]
  rfl
theorem sub4775 (p : Pattern) : d1583 (change p 182 (some 204)) = d4523 p := by
  change (if p 161 then d144 (change p 182 (some 204)) else d1582 (change p 182 (some 204))) = d4523 p
  rw [sub4774, sub4772]
  rfl
theorem sub4776 (p : Pattern) : d1584 (change p 182 (some 204)) = d4518 p := by
  change (if p 163 then d139 (change p 182 (some 204)) else d124 (change p 182 (some 204))) = d4518 p
  rw [sub4769, sub4752]
  rfl
theorem sub4777 (p : Pattern) : d1585 (change p 182 (some 204)) = d4520 p := by
  change (if p 162 then d141 (change p 182 (some 204)) else d1584 (change p 182 (some 204))) = d4520 p
  rw [sub4771, sub4776]
  rfl
theorem sub4778 (p : Pattern) : d1586 (change p 182 (some 204)) = d4523 p := by
  change (if p 161 then d144 (change p 182 (some 204)) else d1585 (change p 182 (some 204))) = d4523 p
  rw [sub4774, sub4777]
  rfl
theorem sub4779 (p : Pattern) : d1587 (change p 182 (some 204)) = d4523 p := by
  change (if p 160 then d1586 (change p 182 (some 204)) else d1583 (change p 182 (some 204))) = d4523 p
  rw [sub4778, sub4775]
  simp only [ite_self]
theorem sub4780 (p : Pattern) : d1588 (change p 182 (some 204)) = d4524 p := by
  change (if p 141 then d1587 (change p 182 (some 204)) else d1579 (change p 182 (some 204))) = d4524 p
  rw [sub4779, sub4764]
  rfl
theorem sub4781 (p : Pattern) : d7 (change p 182 (some 204)) = d7 p := by
  rfl
theorem sub4782 (p : Pattern) : d119 (change p 182 (some 204)) = d119 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d7 (change p 182 (some 204))) = d119 p
  rw [sub4639, sub4781]
  rfl
theorem sub4783 (p : Pattern) : d120 (change p 182 (some 204)) = d120 p := by
  change (if p 246 then d119 (change p 182 (some 204)) else d7 (change p 182 (some 204))) = d120 p
  rw [sub4782, sub4781]
  rfl
theorem sub4784 (p : Pattern) : d229 (change p 182 (some 204)) = d120 p := by
  change d120 (change p 182 (some 204)) = d120 p
  exact sub4783 p
theorem sub4785 (p : Pattern) : d1053 (change p 182 (some 204)) = d4525 p := by
  change (if p 163 then d229 (change p 182 (some 204)) else d139 (change p 182 (some 204))) = d4525 p
  rw [sub4784, sub4769]
  rfl
theorem sub4786 (p : Pattern) : d1054 (change p 182 (some 204)) = d4526 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d1053 (change p 182 (some 204))) = d4526 p
  rw [sub4639, sub4785]
  rfl
theorem sub4787 (p : Pattern) : d1589 (change p 182 (some 204)) = d4527 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1054 (change p 182 (some 204))) = d4527 p
  rw [sub4639, sub4786]
  rfl
theorem sub4788 (p : Pattern) : d1590 (change p 182 (some 204)) = d4528 p := by
  change (if p 160 then d1589 (change p 182 (some 204)) else d1578 (change p 182 (some 204))) = d4528 p
  rw [sub4787, sub4763]
  rfl
theorem sub4789 (p : Pattern) : d230 (change p 182 (some 204)) = d4529 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d229 (change p 182 (some 204))) = d4529 p
  rw [sub4639, sub4784]
  rfl
theorem sub4790 (p : Pattern) : d231 (change p 182 (some 204)) = d4530 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d230 (change p 182 (some 204))) = d4530 p
  rw [sub4639, sub4789]
  rfl
theorem sub4791 (p : Pattern) : d1591 (change p 182 (some 204)) = d4531 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d231 (change p 182 (some 204))) = d4531 p
  rw [sub4639, sub4790]
  rfl
theorem sub4792 (p : Pattern) : d1592 (change p 182 (some 204)) = d4532 p := by
  change (if p 160 then d1591 (change p 182 (some 204)) else d1586 (change p 182 (some 204))) = d4532 p
  rw [sub4791, sub4778]
  rfl
theorem sub4793 (p : Pattern) : d1593 (change p 182 (some 204)) = d4533 p := by
  change (if p 141 then d1592 (change p 182 (some 204)) else d1590 (change p 182 (some 204))) = d4533 p
  rw [sub4792, sub4788]
  rfl
theorem sub4794 (p : Pattern) : d1594 (change p 182 (some 204)) = d4534 p := by
  change (if p 138 then d1593 (change p 182 (some 204)) else d1588 (change p 182 (some 204))) = d4534 p
  rw [sub4793, sub4780]
  rfl
theorem sub4795 (p : Pattern) : d1595 (change p 182 (some 204)) = d4535 p := by
  change (if p 162 then d12 (change p 182 (some 204)) else d128 (change p 182 (some 204))) = d4535 p
  rw [sub4639, sub4759]
  rfl
theorem sub4796 (p : Pattern) : d1596 (change p 182 (some 204)) = d4536 p := by
  change (if p 161 then d12 (change p 182 (some 204)) else d1595 (change p 182 (some 204))) = d4536 p
  rw [sub4639, sub4795]
  rfl
theorem sub4797 (p : Pattern) : d1597 (change p 182 (some 204)) = d4537 p := by
  change (if p 160 then d12 (change p 182 (some 204)) else d1596 (change p 182 (some 204))) = d4537 p
  rw [sub4639, sub4796]
  rfl
theorem sub4798 (p : Pattern) : d1598 (change p 182 (some 204)) = d4538 p := by
  change (if p 141 then d12 (change p 182 (some 204)) else d1597 (change p 182 (some 204))) = d4538 p
  rw [sub4639, sub4797]
  rfl
theorem sub4799 (p : Pattern) : d1599 (change p 182 (some 204)) = d4539 p := by
  change (if p 138 then d1598 (change p 182 (some 204)) else d1593 (change p 182 (some 204))) = d4539 p
  rw [sub4798, sub4793]
  rfl
end NetHack.Sokoban22Refined85
