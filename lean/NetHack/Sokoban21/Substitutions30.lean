/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions29
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4500 (pattern : Twelve) : d1560 (change pattern 11 10) = d2989 pattern := by
  change (if pattern.i then d635 (change pattern 11 10) else d157 (change pattern 11 10)) = d2989 pattern
  rw [s4256, s4245]
  rfl
theorem s4501 (pattern : Twelve) : d1570 (change pattern 11 10) = d2989 pattern := by
  change (if pattern.h then d1560 (change pattern 11 10) else d1559 (change pattern 11 10)) = d2989 pattern
  rw [s4500, s4499]
  simp only [ite_self]
theorem s4502 (pattern : Twelve) : d1585 (change pattern 11 10) = d2990 pattern := by
  change (if pattern.f then d1570 (change pattern 11 10) else d158 (change pattern 11 10)) = d2990 pattern
  rw [s4501, s4240]
  rfl
theorem s4503 (pattern : Twelve) : d1596 (change pattern 11 10) = d2991 pattern := by
  change (if pattern.e then d1577 (change pattern 11 10) else d1585 (change pattern 11 10)) = d2991 pattern
  rw [s4469, s4502]
  rfl
theorem s4504 (pattern : Twelve) : d1571 (change pattern 11 10) = d2973 pattern := by
  change (if pattern.h then d1557 (change pattern 11 10) else d1185 (change pattern 11 10)) = d2973 pattern
  rw [s4471, s4422]
  rfl
theorem s4505 (pattern : Twelve) : d1586 (change pattern 11 10) = d2974 pattern := by
  change (if pattern.f then d1571 (change pattern 11 10) else d692 (change pattern 11 10)) = d2974 pattern
  rw [s4504, s4303]
  rfl
theorem s4506 (pattern : Twelve) : d1597 (change pattern 11 10) = d2976 pattern := by
  change (if pattern.e then d1579 (change pattern 11 10) else d1586 (change pattern 11 10)) = d2976 pattern
  rw [s4475, s4505]
  rfl
theorem s4507 (pattern : Twelve) : d1604 (change pattern 11 10) = d2992 pattern := by
  change (if pattern.j then d1597 (change pattern 11 10) else d1596 (change pattern 11 10)) = d2992 pattern
  rw [s4506, s4503]
  rfl
theorem s4508 (pattern : Twelve) : d1561 (change pattern 11 10) = d2950 pattern := by
  change (if pattern.i then d21 (change pattern 11 10) else d157 (change pattern 11 10)) = d2950 pattern
  rw [s4276, s4245]
  rfl
theorem s4509 (pattern : Twelve) : d1572 (change pattern 11 10) = d2993 pattern := by
  change (if pattern.h then d1561 (change pattern 11 10) else d1185 (change pattern 11 10)) = d2993 pattern
  rw [s4508, s4422]
  rfl
theorem s4510 (pattern : Twelve) : d1587 (change pattern 11 10) = d2994 pattern := by
  change (if pattern.f then d1572 (change pattern 11 10) else d657 (change pattern 11 10)) = d2994 pattern
  rw [s4509, s4283]
  rfl
theorem s4511 (pattern : Twelve) : d1562 (change pattern 11 10) = d2957 pattern := by
  change (if pattern.i then d639 (change pattern 11 10) else d636 (change pattern 11 10)) = d2957 pattern
  rw [s4270, s4258]
  rfl
theorem s4512 (pattern : Twelve) : d1573 (change pattern 11 10) = d2995 pattern := by
  change (if pattern.h then d1562 (change pattern 11 10) else d1184 (change pattern 11 10)) = d2995 pattern
  rw [s4511, s4406]
  rfl
theorem s4513 (pattern : Twelve) : d1588 (change pattern 11 10) = d2996 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1573 (change pattern 11 10)) = d2996 pattern
  rw [s4259, s4512]
  rfl
theorem s4514 (pattern : Twelve) : d1598 (change pattern 11 10) = d2997 pattern := by
  change (if pattern.e then d1588 (change pattern 11 10) else d1587 (change pattern 11 10)) = d2997 pattern
  rw [s4513, s4510]
  rfl
theorem s4515 (pattern : Twelve) : d1574 (change pattern 11 10) = d2998 pattern := by
  change (if pattern.h then d822 (change pattern 11 10) else d670 (change pattern 11 10)) = d2998 pattern
  rw [s4428, s4330]
  rfl
theorem s4516 (pattern : Twelve) : d1589 (change pattern 11 10) = d2999 pattern := by
  change (if pattern.f then d1574 (change pattern 11 10) else d697 (change pattern 11 10)) = d2999 pattern
  rw [s4515, s4327]
  rfl
theorem s4517 (pattern : Twelve) : d1563 (change pattern 11 10) = d47 pattern := by
  change (if pattern.i then d22 (change pattern 11 10) else d644 (change pattern 11 10)) = d47 pattern
  rw [s4280, s4329]
  rfl
theorem s4518 (pattern : Twelve) : d1575 (change pattern 11 10) = d3000 pattern := by
  change (if pattern.h then d679 (change pattern 11 10) else d1563 (change pattern 11 10)) = d3000 pattern
  rw [s4393, s4517]
  rfl
theorem s4519 (pattern : Twelve) : d1590 (change pattern 11 10) = d3001 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1575 (change pattern 11 10)) = d3001 pattern
  rw [s4259, s4518]
  rfl
theorem s4520 (pattern : Twelve) : d1599 (change pattern 11 10) = d3002 pattern := by
  change (if pattern.e then d1590 (change pattern 11 10) else d1589 (change pattern 11 10)) = d3002 pattern
  rw [s4519, s4516]
  rfl
theorem s4521 (pattern : Twelve) : d1605 (change pattern 11 10) = d3003 pattern := by
  change (if pattern.j then d1599 (change pattern 11 10) else d1598 (change pattern 11 10)) = d3003 pattern
  rw [s4520, s4514]
  rfl
theorem s4522 (pattern : Twelve) : d1606 (change pattern 11 10) = d2986 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d1597 (change pattern 11 10)) = d2986 pattern
  rw [s4259, s4506]
  rfl
theorem s4523 (pattern : Twelve) : d1609 (change pattern 11 10) = d3004 pattern := by
  change (if pattern.d then d1606 (change pattern 11 10) else d1605 (change pattern 11 10)) = d3004 pattern
  rw [s4522, s4521]
  rfl
theorem s4524 (pattern : Twelve) : d1612 (change pattern 11 10) = d3005 pattern := by
  change (if pattern.c then d1609 (change pattern 11 10) else d1604 (change pattern 11 10)) = d3005 pattern
  rw [s4523, s4507]
  rfl
theorem s4525 (pattern : Twelve) : d1615 (change pattern 11 10) = d3006 pattern := by
  change (if pattern.a then d1612 (change pattern 11 10) else d1614 (change pattern 11 10)) = d3006 pattern
  rw [s4524, s4498]
  rfl
theorem s4526 (pattern : Twelve) : d1788 (change pattern 11 10) = d3007 pattern := by
  change (if pattern.f then d635 (change pattern 11 10) else d636 (change pattern 11 10)) = d3007 pattern
  rw [s4256, s4258]
  rfl
theorem s4527 (pattern : Twelve) : d1789 (change pattern 11 10) = d3008 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d644 (change pattern 11 10)) = d3008 pattern
  rw [s4259, s4329]
  rfl
theorem s4528 (pattern : Twelve) : d1797 (change pattern 11 10) = d3009 pattern := by
  change (if pattern.e then d1789 (change pattern 11 10) else d1788 (change pattern 11 10)) = d3009 pattern
  rw [s4527, s4526]
  rfl
theorem s4529 (pattern : Twelve) : d1780 (change pattern 11 10) = d38 pattern := by
  change (if pattern.i then d639 (change pattern 11 10) else d635 (change pattern 11 10)) = d38 pattern
  rw [s4270, s4256]
  rfl
theorem s4530 (pattern : Twelve) : d1781 (change pattern 11 10) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d635 (change pattern 11 10)) = d39 pattern
  rw [s4259, s4256]
  rfl
theorem s4531 (pattern : Twelve) : d1784 (change pattern 11 10) = d59 pattern := by
  change (if pattern.h then d1781 (change pattern 11 10) else d1780 (change pattern 11 10)) = d59 pattern
  rw [s4530, s4529]
  rfl
theorem s4532 (pattern : Twelve) : d1790 (change pattern 11 10) = d3010 pattern := by
  change (if pattern.f then d1784 (change pattern 11 10) else d1566 (change pattern 11 10)) = d3010 pattern
  rw [s4531, s4474]
  rfl
theorem s4533 (pattern : Twelve) : d1798 (change pattern 11 10) = d3011 pattern := by
  change (if pattern.e then d1584 (change pattern 11 10) else d1790 (change pattern 11 10)) = d3011 pattern
  rw [s4490, s4532]
  rfl
theorem s4534 (pattern : Twelve) : d1804 (change pattern 11 10) = d3012 pattern := by
  change (if pattern.j then d1798 (change pattern 11 10) else d1797 (change pattern 11 10)) = d3012 pattern
  rw [s4533, s4528]
  rfl
theorem s4535 (pattern : Twelve) : d1791 (change pattern 11 10) = d3013 pattern := by
  change (if pattern.f then d1780 (change pattern 11 10) else d1184 (change pattern 11 10)) = d3013 pattern
  rw [s4529, s4406]
  rfl
theorem s4536 (pattern : Twelve) : d1792 (change pattern 11 10) = d3014 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1186 (change pattern 11 10)) = d3014 pattern
  rw [s4259, s4427]
  rfl
theorem s4537 (pattern : Twelve) : d1799 (change pattern 11 10) = d3015 pattern := by
  change (if pattern.e then d1792 (change pattern 11 10) else d1791 (change pattern 11 10)) = d3015 pattern
  rw [s4536, s4535]
  rfl
theorem s4538 (pattern : Twelve) : d1782 (change pattern 11 10) = d48 pattern := by
  change (if pattern.i then d22 (change pattern 11 10) else d639 (change pattern 11 10)) = d48 pattern
  rw [s4280, s4270]
  rfl
theorem s4539 (pattern : Twelve) : d1785 (change pattern 11 10) = d48 pattern := by
  change (if pattern.h then d679 (change pattern 11 10) else d1782 (change pattern 11 10)) = d48 pattern
  rw [s4393, s4538]
  simp only [ite_self]
theorem s4540 (pattern : Twelve) : d1793 (change pattern 11 10) = d3016 pattern := by
  change (if pattern.f then d1785 (change pattern 11 10) else d1569 (change pattern 11 10)) = d3016 pattern
  rw [s4539, s4489]
  rfl
theorem s4541 (pattern : Twelve) : d1655 (change pattern 11 10) = d3017 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d822 (change pattern 11 10)) = d3017 pattern
  rw [s4259, s4428]
  rfl
theorem s4542 (pattern : Twelve) : d1800 (change pattern 11 10) = d3018 pattern := by
  change (if pattern.e then d1655 (change pattern 11 10) else d1793 (change pattern 11 10)) = d3018 pattern
  rw [s4541, s4540]
  rfl
theorem s4543 (pattern : Twelve) : d1805 (change pattern 11 10) = d3019 pattern := by
  change (if pattern.j then d1800 (change pattern 11 10) else d1799 (change pattern 11 10)) = d3019 pattern
  rw [s4542, s4537]
  rfl
theorem s4544 (pattern : Twelve) : d1806 (change pattern 11 10) = d3020 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d1798 (change pattern 11 10)) = d3020 pattern
  rw [s4259, s4533]
  rfl
theorem s4545 (pattern : Twelve) : d1809 (change pattern 11 10) = d3021 pattern := by
  change (if pattern.d then d1806 (change pattern 11 10) else d1805 (change pattern 11 10)) = d3021 pattern
  rw [s4544, s4543]
  rfl
theorem s4546 (pattern : Twelve) : d1811 (change pattern 11 10) = d3022 pattern := by
  change (if pattern.c then d1809 (change pattern 11 10) else d1804 (change pattern 11 10)) = d3022 pattern
  rw [s4545, s4534]
  rfl
theorem s4547 (pattern : Twelve) : d1794 (change pattern 11 10) = d3023 pattern := by
  change (if pattern.f then d1780 (change pattern 11 10) else d636 (change pattern 11 10)) = d3023 pattern
  rw [s4529, s4258]
  rfl
theorem s4548 (pattern : Twelve) : d1801 (change pattern 11 10) = d3024 pattern := by
  change (if pattern.e then d1789 (change pattern 11 10) else d1794 (change pattern 11 10)) = d3024 pattern
  rw [s4527, s4547]
  rfl
theorem s4549 (pattern : Twelve) : d1807 (change pattern 11 10) = d3025 pattern := by
  change (if pattern.j then d1798 (change pattern 11 10) else d1801 (change pattern 11 10)) = d3025 pattern
  rw [s4533, s4548]
  rfl
theorem s4550 (pattern : Twelve) : d1783 (change pattern 11 10) = d39 pattern := by
  change (if pattern.i then d22 (change pattern 11 10) else d635 (change pattern 11 10)) = d39 pattern
  rw [s4280, s4256]
  rfl
theorem s4551 (pattern : Twelve) : d1786 (change pattern 11 10) = d59 pattern := by
  change (if pattern.h then d1783 (change pattern 11 10) else d1780 (change pattern 11 10)) = d59 pattern
  rw [s4550, s4529]
  rfl
theorem s4552 (pattern : Twelve) : d1795 (change pattern 11 10) = d3026 pattern := by
  change (if pattern.f then d1786 (change pattern 11 10) else d1184 (change pattern 11 10)) = d3026 pattern
  rw [s4551, s4406]
  rfl
theorem s4553 (pattern : Twelve) : d1802 (change pattern 11 10) = d3027 pattern := by
  change (if pattern.e then d1584 (change pattern 11 10) else d1795 (change pattern 11 10)) = d3027 pattern
  rw [s4490, s4552]
  rfl
theorem s4554 (pattern : Twelve) : d183 (change pattern 11 10) = d6 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d22 (change pattern 11 10)) = d6 pattern
  rw [s4259, s4280]
  simp only [ite_self]
theorem s4555 (pattern : Twelve) : d1787 (change pattern 11 10) = d786 pattern := by
  change (if pattern.h then d183 (change pattern 11 10) else d679 (change pattern 11 10)) = d786 pattern
  rw [s4554, s4393]
  rfl
theorem s4556 (pattern : Twelve) : d1796 (change pattern 11 10) = d3028 pattern := by
  change (if pattern.f then d1787 (change pattern 11 10) else d1569 (change pattern 11 10)) = d3028 pattern
  rw [s4555, s4489]
  rfl
theorem s4557 (pattern : Twelve) : d1252 (change pattern 11 10) = d3029 pattern := by
  change (if pattern.h then d6 (change pattern 11 10) else d822 (change pattern 11 10)) = d3029 pattern
  rw [s4259, s4428]
  rfl
theorem s4558 (pattern : Twelve) : d1626 (change pattern 11 10) = d3030 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1252 (change pattern 11 10)) = d3030 pattern
  rw [s4259, s4557]
  rfl
theorem s4559 (pattern : Twelve) : d1803 (change pattern 11 10) = d3031 pattern := by
  change (if pattern.e then d1626 (change pattern 11 10) else d1796 (change pattern 11 10)) = d3031 pattern
  rw [s4558, s4556]
  rfl
theorem s4560 (pattern : Twelve) : d1808 (change pattern 11 10) = d3032 pattern := by
  change (if pattern.j then d1803 (change pattern 11 10) else d1802 (change pattern 11 10)) = d3032 pattern
  rw [s4559, s4553]
  rfl
theorem s4561 (pattern : Twelve) : d1810 (change pattern 11 10) = d3033 pattern := by
  change (if pattern.d then d1806 (change pattern 11 10) else d1808 (change pattern 11 10)) = d3033 pattern
  rw [s4544, s4560]
  rfl
theorem s4562 (pattern : Twelve) : d1812 (change pattern 11 10) = d3034 pattern := by
  change (if pattern.c then d1810 (change pattern 11 10) else d1807 (change pattern 11 10)) = d3034 pattern
  rw [s4561, s4549]
  rfl
theorem s4563 (pattern : Twelve) : d1813 (change pattern 11 10) = d3035 pattern := by
  change (if pattern.a then d1812 (change pattern 11 10) else d1811 (change pattern 11 10)) = d3035 pattern
  rw [s4562, s4546]
  rfl
theorem s4564 (pattern : Twelve) : d0 (change pattern 12 8) = d0 pattern := by
  rfl
theorem s4565 (pattern : Twelve) : d1 (change pattern 12 8) = d1 pattern := by
  rfl
theorem s4566 (pattern : Twelve) : d26 (change pattern 12 8) = d1 pattern := by
  change d1 (change pattern 12 8) = d1 pattern
  exact s4565 pattern
theorem s4567 (pattern : Twelve) : d27 (change pattern 12 8) = d1 pattern := by
  change d1 (change pattern 12 8) = d1 pattern
  exact s4565 pattern
theorem s4568 (pattern : Twelve) : d50 (change pattern 12 8) = d1 pattern := by
  change (if pattern.h then d27 (change pattern 12 8) else d26 (change pattern 12 8)) = d1 pattern
  rw [s4567, s4566]
  simp only [ite_self]
theorem s4569 (pattern : Twelve) : d72 (change pattern 12 8) = d1859 pattern := by
  change (if pattern.f then d50 (change pattern 12 8) else d0 (change pattern 12 8)) = d1859 pattern
  rw [s4568, s4564]
  rfl
theorem s4570 (pattern : Twelve) : d2 (change pattern 12 8) = d2 pattern := by
  rfl
theorem s4571 (pattern : Twelve) : d8 (change pattern 12 8) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 8) else d1 (change pattern 12 8)) = d8 pattern
  rw [s4570, s4565]
  rfl
theorem s4572 (pattern : Twelve) : d3 (change pattern 12 8) = d3 pattern := by
  rfl
theorem s4573 (pattern : Twelve) : d9 (change pattern 12 8) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 8) else d2 (change pattern 12 8)) = d9 pattern
  rw [s4572, s4570]
  rfl
theorem s4574 (pattern : Twelve) : d18 (change pattern 12 8) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 12 8) else d8 (change pattern 12 8)) = d18 pattern
  rw [s4573, s4571]
  rfl
theorem s4575 (pattern : Twelve) : d28 (change pattern 12 8) = d18 pattern := by
  change d18 (change pattern 12 8) = d18 pattern
  exact s4574 pattern
theorem s4576 (pattern : Twelve) : d6 (change pattern 12 8) = d6 pattern := by
  rfl
theorem s4577 (pattern : Twelve) : d29 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4578 (pattern : Twelve) : d51 (change pattern 12 8) = d2281 pattern := by
  change (if pattern.h then d29 (change pattern 12 8) else d28 (change pattern 12 8)) = d2281 pattern
  rw [s4577, s4575]
  rfl
theorem s4579 (pattern : Twelve) : d73 (change pattern 12 8) = d2282 pattern := by
  change (if pattern.f then d51 (change pattern 12 8) else d0 (change pattern 12 8)) = d2282 pattern
  rw [s4578, s4564]
  rfl
theorem s4580 (pattern : Twelve) : d91 (change pattern 12 8) = d2283 pattern := by
  change (if pattern.e then d73 (change pattern 12 8) else d72 (change pattern 12 8)) = d2283 pattern
  rw [s4579, s4569]
  rfl
theorem s4581 (pattern : Twelve) : d30 (change pattern 12 8) = d2 pattern := by
  change d2 (change pattern 12 8) = d2 pattern
  exact s4570 pattern
theorem s4582 (pattern : Twelve) : d5 (change pattern 12 8) = d5 pattern := by
  rfl
theorem s4583 (pattern : Twelve) : d12 (change pattern 12 8) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 8) else d3 (change pattern 12 8)) = d12 pattern
  rw [s4582, s4572]
  rfl
theorem s4584 (pattern : Twelve) : d4 (change pattern 12 8) = d4 pattern := by
  rfl
theorem s4585 (pattern : Twelve) : d13 (change pattern 12 8) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 8) else d4 (change pattern 12 8)) = d13 pattern
  rw [s4576, s4584]
  rfl
theorem s4586 (pattern : Twelve) : d20 (change pattern 12 8) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 8) else d12 (change pattern 12 8)) = d20 pattern
  rw [s4585, s4583]
  rfl
theorem s4587 (pattern : Twelve) : d31 (change pattern 12 8) = d20 pattern := by
  change d20 (change pattern 12 8) = d20 pattern
  exact s4586 pattern
theorem s4588 (pattern : Twelve) : d52 (change pattern 12 8) = d3036 pattern := by
  change (if pattern.h then d31 (change pattern 12 8) else d30 (change pattern 12 8)) = d3036 pattern
  rw [s4587, s4581]
  rfl
theorem s4589 (pattern : Twelve) : d14 (change pattern 12 8) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 8) else d5 (change pattern 12 8)) = d14 pattern
  rw [s4576, s4582]
  rfl
theorem s4590 (pattern : Twelve) : d21 (change pattern 12 8) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 8) else d13 (change pattern 12 8)) = d21 pattern
  rw [s4589, s4585]
  rfl
theorem s4591 (pattern : Twelve) : d32 (change pattern 12 8) = d21 pattern := by
  change d21 (change pattern 12 8) = d21 pattern
  exact s4590 pattern
theorem s4592 (pattern : Twelve) : d53 (change pattern 12 8) = d3037 pattern := by
  change (if pattern.h then d32 (change pattern 12 8) else d30 (change pattern 12 8)) = d3037 pattern
  rw [s4591, s4581]
  rfl
theorem s4593 (pattern : Twelve) : d74 (change pattern 12 8) = d3038 pattern := by
  change (if pattern.f then d53 (change pattern 12 8) else d52 (change pattern 12 8)) = d3038 pattern
  rw [s4592, s4588]
  rfl
theorem s4594 (pattern : Twelve) : d22 (change pattern 12 8) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 8) else d14 (change pattern 12 8)) = d22 pattern
  rw [s4576, s4589]
  rfl
theorem s4595 (pattern : Twelve) : d33 (change pattern 12 8) = d22 pattern := by
  change d22 (change pattern 12 8) = d22 pattern
  exact s4594 pattern
theorem s4596 (pattern : Twelve) : d54 (change pattern 12 8) = d3039 pattern := by
  change (if pattern.h then d33 (change pattern 12 8) else d30 (change pattern 12 8)) = d3039 pattern
  rw [s4595, s4581]
  rfl
theorem s4597 (pattern : Twelve) : d23 (change pattern 12 8) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 8) else d2 (change pattern 12 8)) = d23 pattern
  rw [s4573, s4570]
  rfl
theorem s4598 (pattern : Twelve) : d34 (change pattern 12 8) = d23 pattern := by
  change d23 (change pattern 12 8) = d23 pattern
  exact s4597 pattern
theorem s4599 (pattern : Twelve) : d55 (change pattern 12 8) = d2284 pattern := by
  change (if pattern.h then d29 (change pattern 12 8) else d34 (change pattern 12 8)) = d2284 pattern
  rw [s4577, s4598]
  rfl
theorem s4600 (pattern : Twelve) : d75 (change pattern 12 8) = d3040 pattern := by
  change (if pattern.f then d55 (change pattern 12 8) else d54 (change pattern 12 8)) = d3040 pattern
  rw [s4599, s4596]
  rfl
theorem s4601 (pattern : Twelve) : d92 (change pattern 12 8) = d3041 pattern := by
  change (if pattern.e then d75 (change pattern 12 8) else d74 (change pattern 12 8)) = d3041 pattern
  rw [s4600, s4593]
  rfl
theorem s4602 (pattern : Twelve) : d102 (change pattern 12 8) = d3042 pattern := by
  change (if pattern.j then d92 (change pattern 12 8) else d91 (change pattern 12 8)) = d3042 pattern
  rw [s4601, s4580]
  rfl
theorem s4603 (pattern : Twelve) : d76 (change pattern 12 8) = d2285 pattern := by
  change (if pattern.f then d55 (change pattern 12 8) else d0 (change pattern 12 8)) = d2285 pattern
  rw [s4599, s4564]
  rfl
theorem s4604 (pattern : Twelve) : d93 (change pattern 12 8) = d2286 pattern := by
  change (if pattern.e then d76 (change pattern 12 8) else d72 (change pattern 12 8)) = d2286 pattern
  rw [s4603, s4569]
  rfl
theorem s4605 (pattern : Twelve) : d35 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4606 (pattern : Twelve) : d56 (change pattern 12 8) = d3043 pattern := by
  change (if pattern.h then d35 (change pattern 12 8) else d30 (change pattern 12 8)) = d3043 pattern
  rw [s4605, s4581]
  rfl
theorem s4607 (pattern : Twelve) : d36 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4608 (pattern : Twelve) : d57 (change pattern 12 8) = d3043 pattern := by
  change (if pattern.h then d36 (change pattern 12 8) else d30 (change pattern 12 8)) = d3043 pattern
  rw [s4607, s4581]
  rfl
theorem s4609 (pattern : Twelve) : d77 (change pattern 12 8) = d3043 pattern := by
  change (if pattern.f then d57 (change pattern 12 8) else d56 (change pattern 12 8)) = d3043 pattern
  rw [s4608, s4606]
  simp only [ite_self]
theorem s4610 (pattern : Twelve) : d78 (change pattern 12 8) = d3044 pattern := by
  change (if pattern.f then d55 (change pattern 12 8) else d56 (change pattern 12 8)) = d3044 pattern
  rw [s4599, s4606]
  rfl
theorem s4611 (pattern : Twelve) : d94 (change pattern 12 8) = d3045 pattern := by
  change (if pattern.e then d78 (change pattern 12 8) else d77 (change pattern 12 8)) = d3045 pattern
  rw [s4610, s4609]
  rfl
theorem s4612 (pattern : Twelve) : d103 (change pattern 12 8) = d3046 pattern := by
  change (if pattern.j then d94 (change pattern 12 8) else d93 (change pattern 12 8)) = d3046 pattern
  rw [s4611, s4604]
  rfl
theorem s4613 (pattern : Twelve) : d110 (change pattern 12 8) = d3047 pattern := by
  change (if pattern.d then d103 (change pattern 12 8) else d102 (change pattern 12 8)) = d3047 pattern
  rw [s4612, s4602]
  rfl
theorem s4614 (pattern : Twelve) : d37 (change pattern 12 8) = d3 pattern := by
  change d3 (change pattern 12 8) = d3 pattern
  exact s4572 pattern
theorem s4615 (pattern : Twelve) : d58 (change pattern 12 8) = d2427 pattern := by
  change (if pattern.h then d37 (change pattern 12 8) else d30 (change pattern 12 8)) = d2427 pattern
  rw [s4614, s4581]
  rfl
theorem s4616 (pattern : Twelve) : d79 (change pattern 12 8) = d3048 pattern := by
  change (if pattern.f then d58 (change pattern 12 8) else d30 (change pattern 12 8)) = d3048 pattern
  rw [s4615, s4581]
  rfl
theorem s4617 (pattern : Twelve) : d80 (change pattern 12 8) = d2288 pattern := by
  change (if pattern.f then d55 (change pattern 12 8) else d30 (change pattern 12 8)) = d2288 pattern
  rw [s4599, s4581]
  rfl
theorem s4618 (pattern : Twelve) : d95 (change pattern 12 8) = d3049 pattern := by
  change (if pattern.e then d80 (change pattern 12 8) else d79 (change pattern 12 8)) = d3049 pattern
  rw [s4617, s4616]
  rfl
theorem s4619 (pattern : Twelve) : d38 (change pattern 12 8) = d4 pattern := by
  change d4 (change pattern 12 8) = d4 pattern
  exact s4584 pattern
theorem s4620 (pattern : Twelve) : d39 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4621 (pattern : Twelve) : d59 (change pattern 12 8) = d3050 pattern := by
  change (if pattern.h then d39 (change pattern 12 8) else d38 (change pattern 12 8)) = d3050 pattern
  rw [s4620, s4619]
  rfl
theorem s4622 (pattern : Twelve) : d40 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4623 (pattern : Twelve) : d60 (change pattern 12 8) = d3050 pattern := by
  change (if pattern.h then d40 (change pattern 12 8) else d38 (change pattern 12 8)) = d3050 pattern
  rw [s4622, s4619]
  rfl
theorem s4624 (pattern : Twelve) : d81 (change pattern 12 8) = d3050 pattern := by
  change (if pattern.f then d60 (change pattern 12 8) else d59 (change pattern 12 8)) = d3050 pattern
  rw [s4623, s4621]
  simp only [ite_self]
theorem s4625 (pattern : Twelve) : d15 (change pattern 12 8) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 8) else d4 (change pattern 12 8)) = d15 pattern
  rw [s4582, s4584]
  rfl
theorem s4626 (pattern : Twelve) : d24 (change pattern 12 8) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 8) else d4 (change pattern 12 8)) = d24 pattern
  rw [s4625, s4584]
  rfl
theorem s4627 (pattern : Twelve) : d41 (change pattern 12 8) = d24 pattern := by
  change d24 (change pattern 12 8) = d24 pattern
  exact s4626 pattern
theorem s4628 (pattern : Twelve) : d42 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4629 (pattern : Twelve) : d61 (change pattern 12 8) = d3051 pattern := by
  change (if pattern.h then d42 (change pattern 12 8) else d41 (change pattern 12 8)) = d3051 pattern
  rw [s4628, s4627]
  rfl
theorem s4630 (pattern : Twelve) : d82 (change pattern 12 8) = d3052 pattern := by
  change (if pattern.f then d61 (change pattern 12 8) else d59 (change pattern 12 8)) = d3052 pattern
  rw [s4629, s4621]
  rfl
theorem s4631 (pattern : Twelve) : d96 (change pattern 12 8) = d3053 pattern := by
  change (if pattern.e then d82 (change pattern 12 8) else d81 (change pattern 12 8)) = d3053 pattern
  rw [s4630, s4624]
  rfl
theorem s4632 (pattern : Twelve) : d104 (change pattern 12 8) = d3054 pattern := by
  change (if pattern.j then d96 (change pattern 12 8) else d95 (change pattern 12 8)) = d3054 pattern
  rw [s4631, s4618]
  rfl
theorem s4633 (pattern : Twelve) : d105 (change pattern 12 8) = d3055 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d94 (change pattern 12 8)) = d3055 pattern
  rw [s4576, s4611]
  rfl
theorem s4634 (pattern : Twelve) : d111 (change pattern 12 8) = d3056 pattern := by
  change (if pattern.d then d105 (change pattern 12 8) else d104 (change pattern 12 8)) = d3056 pattern
  rw [s4633, s4632]
  rfl
theorem s4635 (pattern : Twelve) : d114 (change pattern 12 8) = d3057 pattern := by
  change (if pattern.c then d111 (change pattern 12 8) else d110 (change pattern 12 8)) = d3057 pattern
  rw [s4634, s4613]
  rfl
theorem s4636 (pattern : Twelve) : d16 (change pattern 12 8) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 8) else d2 (change pattern 12 8)) = d16 pattern
  rw [s4584, s4570]
  rfl
theorem s4637 (pattern : Twelve) : d25 (change pattern 12 8) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 8) else d16 (change pattern 12 8)) = d25 pattern
  rw [s4583, s4636]
  rfl
theorem s4638 (pattern : Twelve) : d120 (change pattern 12 8) = d25 pattern := by
  change d25 (change pattern 12 8) = d25 pattern
  exact s4637 pattern
theorem s4639 (pattern : Twelve) : d129 (change pattern 12 8) = d1690 pattern := by
  change (if pattern.h then d29 (change pattern 12 8) else d120 (change pattern 12 8)) = d1690 pattern
  rw [s4577, s4638]
  rfl
theorem s4640 (pattern : Twelve) : d136 (change pattern 12 8) = d3058 pattern := by
  change (if pattern.f then d129 (change pattern 12 8) else d0 (change pattern 12 8)) = d3058 pattern
  rw [s4639, s4564]
  rfl
theorem s4641 (pattern : Twelve) : d144 (change pattern 12 8) = d3059 pattern := by
  change (if pattern.e then d136 (change pattern 12 8) else d72 (change pattern 12 8)) = d3059 pattern
  rw [s4640, s4569]
  rfl
theorem s4642 (pattern : Twelve) : d121 (change pattern 12 8) = d23 pattern := by
  change d23 (change pattern 12 8) = d23 pattern
  exact s4597 pattern
theorem s4643 (pattern : Twelve) : d130 (change pattern 12 8) = d2284 pattern := by
  change (if pattern.h then d36 (change pattern 12 8) else d121 (change pattern 12 8)) = d2284 pattern
  rw [s4607, s4642]
  rfl
theorem s4644 (pattern : Twelve) : d137 (change pattern 12 8) = d3060 pattern := by
  change (if pattern.f then d130 (change pattern 12 8) else d52 (change pattern 12 8)) = d3060 pattern
  rw [s4643, s4588]
  rfl
theorem s4645 (pattern : Twelve) : d138 (change pattern 12 8) = d3061 pattern := by
  change (if pattern.f then d129 (change pattern 12 8) else d56 (change pattern 12 8)) = d3061 pattern
  rw [s4639, s4606]
  rfl
theorem s4646 (pattern : Twelve) : d145 (change pattern 12 8) = d3062 pattern := by
  change (if pattern.e then d138 (change pattern 12 8) else d137 (change pattern 12 8)) = d3062 pattern
  rw [s4645, s4644]
  rfl
theorem s4647 (pattern : Twelve) : d149 (change pattern 12 8) = d3063 pattern := by
  change (if pattern.j then d145 (change pattern 12 8) else d144 (change pattern 12 8)) = d3063 pattern
  rw [s4646, s4641]
  rfl
theorem s4648 (pattern : Twelve) : d139 (change pattern 12 8) = d3044 pattern := by
  change (if pattern.f then d130 (change pattern 12 8) else d56 (change pattern 12 8)) = d3044 pattern
  rw [s4643, s4606]
  rfl
theorem s4649 (pattern : Twelve) : d146 (change pattern 12 8) = d3064 pattern := by
  change (if pattern.e then d138 (change pattern 12 8) else d139 (change pattern 12 8)) = d3064 pattern
  rw [s4645, s4648]
  rfl
end NetHack.Sokoban21.Diagram
