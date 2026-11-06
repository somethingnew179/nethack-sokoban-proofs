/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions31
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4800 (pattern : Twelve) : d1330 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4801 (pattern : Twelve) : d1331 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4802 (pattern : Twelve) : d1337 (change pattern 12 8) = d6 pattern := by
  change (if pattern.h then d1331 (change pattern 12 8) else d1330 (change pattern 12 8)) = d6 pattern
  rw [s4801, s4800]
  simp only [ite_self]
theorem s4803 (pattern : Twelve) : d1343 (change pattern 12 8) = d3135 pattern := by
  change (if pattern.f then d1337 (change pattern 12 8) else d830 (change pattern 12 8)) = d3135 pattern
  rw [s4802, s4701]
  rfl
theorem s4804 (pattern : Twelve) : d1332 (change pattern 12 8) = d22 pattern := by
  change d22 (change pattern 12 8) = d22 pattern
  exact s4594 pattern
theorem s4805 (pattern : Twelve) : d1338 (change pattern 12 8) = d3074 pattern := by
  change (if pattern.h then d128 (change pattern 12 8) else d1332 (change pattern 12 8)) = d3074 pattern
  rw [s4668, s4804]
  rfl
theorem s4806 (pattern : Twelve) : d1344 (change pattern 12 8) = d3136 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d1338 (change pattern 12 8)) = d3136 pattern
  rw [s4576, s4805]
  rfl
theorem s4807 (pattern : Twelve) : d1348 (change pattern 12 8) = d3137 pattern := by
  change (if pattern.e then d1344 (change pattern 12 8) else d1343 (change pattern 12 8)) = d3137 pattern
  rw [s4806, s4803]
  rfl
theorem s4808 (pattern : Twelve) : d1350 (change pattern 12 8) = d3138 pattern := by
  change (if pattern.j then d1348 (change pattern 12 8) else d1347 (change pattern 12 8)) = d3138 pattern
  rw [s4807, s4799]
  rfl
theorem s4809 (pattern : Twelve) : d1351 (change pattern 12 8) = d3139 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d1346 (change pattern 12 8)) = d3139 pattern
  rw [s4576, s4791]
  rfl
theorem s4810 (pattern : Twelve) : d1352 (change pattern 12 8) = d3140 pattern := by
  change (if pattern.d then d1351 (change pattern 12 8) else d1350 (change pattern 12 8)) = d3140 pattern
  rw [s4809, s4808]
  rfl
theorem s4811 (pattern : Twelve) : d1353 (change pattern 12 8) = d3141 pattern := by
  change (if pattern.c then d1352 (change pattern 12 8) else d1349 (change pattern 12 8)) = d3141 pattern
  rw [s4810, s4792]
  rfl
theorem s4812 (pattern : Twelve) : d1354 (change pattern 12 8) = d3142 pattern := by
  change (if pattern.a then d1353 (change pattern 12 8) else d1321 (change pattern 12 8)) = d3142 pattern
  rw [s4811, s4781]
  rfl
theorem s4813 (pattern : Twelve) : d1649 (change pattern 12 8) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 8) else d19 (change pattern 12 8)) = d1649 pattern
  rw [s4782, s4754]
  rfl
theorem s4814 (pattern : Twelve) : d1650 (change pattern 12 8) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d25 (change pattern 12 8)) = d1650 pattern
  rw [s4576, s4637]
  rfl
theorem s4815 (pattern : Twelve) : d1656 (change pattern 12 8) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 8) else d1649 (change pattern 12 8)) = d1656 pattern
  rw [s4814, s4813]
  rfl
theorem s4816 (pattern : Twelve) : d1644 (change pattern 12 8) = d20 pattern := by
  change d20 (change pattern 12 8) = d20 pattern
  exact s4586 pattern
theorem s4817 (pattern : Twelve) : d1645 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4818 (pattern : Twelve) : d1647 (change pattern 12 8) = d3143 pattern := by
  change (if pattern.h then d1645 (change pattern 12 8) else d1644 (change pattern 12 8)) = d3143 pattern
  rw [s4817, s4816]
  rfl
theorem s4819 (pattern : Twelve) : d1651 (change pattern 12 8) = d3144 pattern := by
  change (if pattern.f then d1647 (change pattern 12 8) else d1286 (change pattern 12 8)) = d3144 pattern
  rw [s4818, s4762]
  rfl
theorem s4820 (pattern : Twelve) : d1657 (change pattern 12 8) = d3145 pattern := by
  change (if pattern.e then d1300 (change pattern 12 8) else d1651 (change pattern 12 8)) = d3145 pattern
  rw [s4776, s4819]
  rfl
theorem s4821 (pattern : Twelve) : d1660 (change pattern 12 8) = d3146 pattern := by
  change (if pattern.j then d1657 (change pattern 12 8) else d1656 (change pattern 12 8)) = d3146 pattern
  rw [s4820, s4815]
  rfl
theorem s4822 (pattern : Twelve) : d1652 (change pattern 12 8) = d1814 pattern := by
  change (if pattern.f then d1644 (change pattern 12 8) else d817 (change pattern 12 8)) = d1814 pattern
  rw [s4816, s4682]
  rfl
theorem s4823 (pattern : Twelve) : d1653 (change pattern 12 8) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d821 (change pattern 12 8)) = d1815 pattern
  rw [s4576, s4702]
  rfl
theorem s4824 (pattern : Twelve) : d1658 (change pattern 12 8) = d1818 pattern := by
  change (if pattern.e then d1653 (change pattern 12 8) else d1652 (change pattern 12 8)) = d1818 pattern
  rw [s4823, s4822]
  rfl
theorem s4825 (pattern : Twelve) : d1646 (change pattern 12 8) = d22 pattern := by
  change d22 (change pattern 12 8) = d22 pattern
  exact s4594 pattern
theorem s4826 (pattern : Twelve) : d1648 (change pattern 12 8) = d3074 pattern := by
  change (if pattern.h then d128 (change pattern 12 8) else d1646 (change pattern 12 8)) = d3074 pattern
  rw [s4668, s4825]
  rfl
theorem s4827 (pattern : Twelve) : d1654 (change pattern 12 8) = d3147 pattern := by
  change (if pattern.f then d1648 (change pattern 12 8) else d1289 (change pattern 12 8)) = d3147 pattern
  rw [s4826, s4775]
  rfl
theorem s4828 (pattern : Twelve) : d1655 (change pattern 12 8) = d6 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d822 (change pattern 12 8)) = d6 pattern
  rw [s4576, s4703]
  simp only [ite_self]
theorem s4829 (pattern : Twelve) : d1659 (change pattern 12 8) = d3148 pattern := by
  change (if pattern.e then d1655 (change pattern 12 8) else d1654 (change pattern 12 8)) = d3148 pattern
  rw [s4828, s4827]
  rfl
theorem s4830 (pattern : Twelve) : d1661 (change pattern 12 8) = d3149 pattern := by
  change (if pattern.j then d1659 (change pattern 12 8) else d1658 (change pattern 12 8)) = d3149 pattern
  rw [s4829, s4824]
  rfl
theorem s4831 (pattern : Twelve) : d1662 (change pattern 12 8) = d3150 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d1657 (change pattern 12 8)) = d3150 pattern
  rw [s4576, s4820]
  rfl
theorem s4832 (pattern : Twelve) : d1663 (change pattern 12 8) = d3151 pattern := by
  change (if pattern.d then d1662 (change pattern 12 8) else d1661 (change pattern 12 8)) = d3151 pattern
  rw [s4831, s4830]
  rfl
theorem s4833 (pattern : Twelve) : d1664 (change pattern 12 8) = d3152 pattern := by
  change (if pattern.c then d1663 (change pattern 12 8) else d1660 (change pattern 12 8)) = d3152 pattern
  rw [s4832, s4821]
  rfl
theorem s4834 (pattern : Twelve) : d1668 (change pattern 12 8) = d3153 pattern := by
  change (if pattern.f then d1644 (change pattern 12 8) else d19 (change pattern 12 8)) = d3153 pattern
  rw [s4816, s4754]
  rfl
theorem s4835 (pattern : Twelve) : d1671 (change pattern 12 8) = d3154 pattern := by
  change (if pattern.e then d1650 (change pattern 12 8) else d1668 (change pattern 12 8)) = d3154 pattern
  rw [s4814, s4834]
  rfl
theorem s4836 (pattern : Twelve) : d1674 (change pattern 12 8) = d3155 pattern := by
  change (if pattern.j then d1657 (change pattern 12 8) else d1671 (change pattern 12 8)) = d3155 pattern
  rw [s4820, s4835]
  rfl
theorem s4837 (pattern : Twelve) : d1665 (change pattern 12 8) = d22 pattern := by
  change d22 (change pattern 12 8) = d22 pattern
  exact s4594 pattern
theorem s4838 (pattern : Twelve) : d1666 (change pattern 12 8) = d2410 pattern := by
  change (if pattern.h then d1665 (change pattern 12 8) else d1644 (change pattern 12 8)) = d2410 pattern
  rw [s4837, s4816]
  rfl
theorem s4839 (pattern : Twelve) : d1669 (change pattern 12 8) = d2468 pattern := by
  change (if pattern.f then d1666 (change pattern 12 8) else d817 (change pattern 12 8)) = d2468 pattern
  rw [s4838, s4682]
  rfl
theorem s4840 (pattern : Twelve) : d1672 (change pattern 12 8) = d2471 pattern := by
  change (if pattern.e then d1300 (change pattern 12 8) else d1669 (change pattern 12 8)) = d2471 pattern
  rw [s4776, s4839]
  rfl
theorem s4841 (pattern : Twelve) : d183 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4842 (pattern : Twelve) : d1667 (change pattern 12 8) = d6 pattern := by
  change (if pattern.h then d183 (change pattern 12 8) else d128 (change pattern 12 8)) = d6 pattern
  rw [s4841, s4668]
  simp only [ite_self]
theorem s4843 (pattern : Twelve) : d1670 (change pattern 12 8) = d2470 pattern := by
  change (if pattern.f then d1667 (change pattern 12 8) else d1289 (change pattern 12 8)) = d2470 pattern
  rw [s4842, s4775]
  rfl
theorem s4844 (pattern : Twelve) : d1252 (change pattern 12 8) = d6 pattern := by
  change (if pattern.h then d6 (change pattern 12 8) else d822 (change pattern 12 8)) = d6 pattern
  rw [s4576, s4703]
  simp only [ite_self]
theorem s4845 (pattern : Twelve) : d1626 (change pattern 12 8) = d6 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d1252 (change pattern 12 8)) = d6 pattern
  rw [s4576, s4844]
  simp only [ite_self]
theorem s4846 (pattern : Twelve) : d1673 (change pattern 12 8) = d3156 pattern := by
  change (if pattern.e then d1626 (change pattern 12 8) else d1670 (change pattern 12 8)) = d3156 pattern
  rw [s4845, s4843]
  rfl
theorem s4847 (pattern : Twelve) : d1675 (change pattern 12 8) = d3157 pattern := by
  change (if pattern.j then d1673 (change pattern 12 8) else d1672 (change pattern 12 8)) = d3157 pattern
  rw [s4846, s4840]
  rfl
theorem s4848 (pattern : Twelve) : d1676 (change pattern 12 8) = d3158 pattern := by
  change (if pattern.d then d1662 (change pattern 12 8) else d1675 (change pattern 12 8)) = d3158 pattern
  rw [s4831, s4847]
  rfl
theorem s4849 (pattern : Twelve) : d1677 (change pattern 12 8) = d3159 pattern := by
  change (if pattern.c then d1676 (change pattern 12 8) else d1674 (change pattern 12 8)) = d3159 pattern
  rw [s4848, s4836]
  rfl
theorem s4850 (pattern : Twelve) : d1678 (change pattern 12 8) = d3160 pattern := by
  change (if pattern.a then d1677 (change pattern 12 8) else d1664 (change pattern 12 8)) = d3160 pattern
  rw [s4849, s4833]
  rfl
theorem s4851 (pattern : Twelve) : d120 (change pattern 12 12) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 12 12) else d17 (change pattern 12 12)) = d120 pattern
  rw [s18, s3]
  rfl
theorem s4852 (pattern : Twelve) : d129 (change pattern 12 12) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 12 12) else d120 (change pattern 12 12)) = d129 pattern
  rw [s110, s4851]
  rfl
theorem s4853 (pattern : Twelve) : d136 (change pattern 12 12) = d136 pattern := by
  change (if pattern.f then d129 (change pattern 12 12) else d0 (change pattern 12 12)) = d136 pattern
  rw [s4852, s0]
  rfl
theorem s4854 (pattern : Twelve) : d144 (change pattern 12 12) = d144 pattern := by
  change (if pattern.e then d136 (change pattern 12 12) else d72 (change pattern 12 12)) = d144 pattern
  rw [s4853, s336]
  rfl
theorem s4855 (pattern : Twelve) : d121 (change pattern 12 12) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 12 12) else d0 (change pattern 12 12)) = d121 pattern
  rw [s29, s0]
  rfl
theorem s4856 (pattern : Twelve) : d130 (change pattern 12 12) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 12 12) else d121 (change pattern 12 12)) = d130 pattern
  rw [s34, s4855]
  rfl
theorem s4857 (pattern : Twelve) : d137 (change pattern 12 12) = d137 pattern := by
  change (if pattern.f then d130 (change pattern 12 12) else d52 (change pattern 12 12)) = d137 pattern
  rw [s4856, s343]
  rfl
theorem s4858 (pattern : Twelve) : d138 (change pattern 12 12) = d138 pattern := by
  change (if pattern.f then d129 (change pattern 12 12) else d56 (change pattern 12 12)) = d138 pattern
  rw [s4852, s27]
  rfl
theorem s4859 (pattern : Twelve) : d145 (change pattern 12 12) = d145 pattern := by
  change (if pattern.e then d138 (change pattern 12 12) else d137 (change pattern 12 12)) = d145 pattern
  rw [s4858, s4857]
  rfl
theorem s4860 (pattern : Twelve) : d149 (change pattern 12 12) = d149 pattern := by
  change (if pattern.j then d145 (change pattern 12 12) else d144 (change pattern 12 12)) = d149 pattern
  rw [s4859, s4854]
  rfl
theorem s4861 (pattern : Twelve) : d139 (change pattern 12 12) = d139 pattern := by
  change (if pattern.f then d130 (change pattern 12 12) else d56 (change pattern 12 12)) = d139 pattern
  rw [s4856, s27]
  rfl
theorem s4862 (pattern : Twelve) : d146 (change pattern 12 12) = d146 pattern := by
  change (if pattern.e then d138 (change pattern 12 12) else d139 (change pattern 12 12)) = d146 pattern
  rw [s4858, s4861]
  rfl
theorem s4863 (pattern : Twelve) : d150 (change pattern 12 12) = d150 pattern := by
  change (if pattern.j then d146 (change pattern 12 12) else d144 (change pattern 12 12)) = d150 pattern
  rw [s4862, s4854]
  rfl
theorem s4864 (pattern : Twelve) : d153 (change pattern 12 12) = d153 pattern := by
  change (if pattern.d then d150 (change pattern 12 12) else d149 (change pattern 12 12)) = d153 pattern
  rw [s4863, s4860]
  rfl
theorem s4865 (pattern : Twelve) : d122 (change pattern 12 12) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 12 12) else d17 (change pattern 12 12)) = d122 pattern
  rw [s14, s3]
  rfl
theorem s4866 (pattern : Twelve) : d131 (change pattern 12 12) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 12 12) else d121 (change pattern 12 12)) = d131 pattern
  rw [s4865, s4855]
  rfl
theorem s4867 (pattern : Twelve) : d140 (change pattern 12 12) = d140 pattern := by
  change (if pattern.f then d131 (change pattern 12 12) else d30 (change pattern 12 12)) = d140 pattern
  rw [s4866, s25]
  rfl
theorem s4868 (pattern : Twelve) : d123 (change pattern 12 12) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d0 (change pattern 12 12)) = d123 pattern
  rw [s11, s0]
  rfl
theorem s4869 (pattern : Twelve) : d132 (change pattern 12 12) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 12 12) else d30 (change pattern 12 12)) = d132 pattern
  rw [s4868, s25]
  rfl
theorem s4870 (pattern : Twelve) : d141 (change pattern 12 12) = d141 pattern := by
  change (if pattern.f then d129 (change pattern 12 12) else d132 (change pattern 12 12)) = d141 pattern
  rw [s4852, s4869]
  rfl
theorem s4871 (pattern : Twelve) : d147 (change pattern 12 12) = d147 pattern := by
  change (if pattern.e then d141 (change pattern 12 12) else d140 (change pattern 12 12)) = d147 pattern
  rw [s4870, s4867]
  rfl
theorem s4872 (pattern : Twelve) : d124 (change pattern 12 12) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 12 12) else d2 (change pattern 12 12)) = d124 pattern
  rw [s203, s9]
  rfl
theorem s4873 (pattern : Twelve) : d133 (change pattern 12 12) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 12 12) else d124 (change pattern 12 12)) = d133 pattern
  rw [s123, s4872]
  rfl
theorem s4874 (pattern : Twelve) : d142 (change pattern 12 12) = d142 pattern := by
  change (if pattern.f then d133 (change pattern 12 12) else d59 (change pattern 12 12)) = d142 pattern
  rw [s4873, s46]
  rfl
theorem s4875 (pattern : Twelve) : d126 (change pattern 12 12) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 12 12) else d2 (change pattern 12 12)) = d126 pattern
  rw [s16, s9]
  rfl
theorem s4876 (pattern : Twelve) : d134 (change pattern 12 12) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 12 12) else d126 (change pattern 12 12)) = d134 pattern
  rw [s84, s4875]
  rfl
theorem s4877 (pattern : Twelve) : d135 (change pattern 12 12) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 12 12) else d127 (change pattern 12 12)) = d135 pattern
  rw [s168, s198]
  rfl
theorem s4878 (pattern : Twelve) : d143 (change pattern 12 12) = d143 pattern := by
  change (if pattern.f then d135 (change pattern 12 12) else d134 (change pattern 12 12)) = d143 pattern
  rw [s4877, s4876]
  rfl
theorem s4879 (pattern : Twelve) : d148 (change pattern 12 12) = d148 pattern := by
  change (if pattern.e then d143 (change pattern 12 12) else d142 (change pattern 12 12)) = d148 pattern
  rw [s4878, s4874]
  rfl
theorem s4880 (pattern : Twelve) : d151 (change pattern 12 12) = d151 pattern := by
  change (if pattern.j then d148 (change pattern 12 12) else d147 (change pattern 12 12)) = d151 pattern
  rw [s4879, s4871]
  rfl
theorem s4881 (pattern : Twelve) : d152 (change pattern 12 12) = d152 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d146 (change pattern 12 12)) = d152 pattern
  rw [s20, s4862]
  rfl
theorem s4882 (pattern : Twelve) : d154 (change pattern 12 12) = d154 pattern := by
  change (if pattern.d then d152 (change pattern 12 12) else d151 (change pattern 12 12)) = d154 pattern
  rw [s4881, s4880]
  rfl
theorem s4883 (pattern : Twelve) : d155 (change pattern 12 12) = d155 pattern := by
  change (if pattern.c then d154 (change pattern 12 12) else d153 (change pattern 12 12)) = d155 pattern
  rw [s4882, s4864]
  rfl
theorem s4884 (pattern : Twelve) : d156 (change pattern 12 12) = d156 pattern := by
  change (if pattern.a then d155 (change pattern 12 12) else d114 (change pattern 12 12)) = d156 pattern
  rw [s4883, s374]
  rfl
theorem s4885 (pattern : Twelve) : d0 (change pattern 12 5) = d0 pattern := by
  rfl
theorem s4886 (pattern : Twelve) : d1 (change pattern 12 5) = d1 pattern := by
  rfl
theorem s4887 (pattern : Twelve) : d26 (change pattern 12 5) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 5) else d0 (change pattern 12 5)) = d26 pattern
  rw [s4886, s4885]
  rfl
theorem s4888 (pattern : Twelve) : d7 (change pattern 12 5) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 5) else d0 (change pattern 12 5)) = d7 pattern
  rw [s4886, s4885]
  rfl
theorem s4889 (pattern : Twelve) : d17 (change pattern 12 5) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 5) else d0 (change pattern 12 5)) = d17 pattern
  rw [s4888, s4885]
  rfl
theorem s4890 (pattern : Twelve) : d27 (change pattern 12 5) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 5) else d17 (change pattern 12 5)) = d27 pattern
  rw [s4886, s4889]
  rfl
theorem s4891 (pattern : Twelve) : d50 (change pattern 12 5) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 5) else d26 (change pattern 12 5)) = d50 pattern
  rw [s4890, s4887]
  rfl
theorem s4892 (pattern : Twelve) : d72 (change pattern 12 5) = d50 pattern := by
  change d50 (change pattern 12 5) = d50 pattern
  exact s4891 pattern
theorem s4893 (pattern : Twelve) : d2 (change pattern 12 5) = d2 pattern := by
  rfl
theorem s4894 (pattern : Twelve) : d8 (change pattern 12 5) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 5) else d1 (change pattern 12 5)) = d8 pattern
  rw [s4893, s4886]
  rfl
theorem s4895 (pattern : Twelve) : d3 (change pattern 12 5) = d3 pattern := by
  rfl
theorem s4896 (pattern : Twelve) : d9 (change pattern 12 5) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 5) else d2 (change pattern 12 5)) = d9 pattern
  rw [s4895, s4893]
  rfl
theorem s4897 (pattern : Twelve) : d18 (change pattern 12 5) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 12 5) else d8 (change pattern 12 5)) = d18 pattern
  rw [s4896, s4894]
  rfl
theorem s4898 (pattern : Twelve) : d28 (change pattern 12 5) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 12 5) else d17 (change pattern 12 5)) = d28 pattern
  rw [s4897, s4889]
  rfl
theorem s4899 (pattern : Twelve) : d10 (change pattern 12 5) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 5) else d0 (change pattern 12 5)) = d10 pattern
  rw [s4893, s4885]
  rfl
theorem s4900 (pattern : Twelve) : d11 (change pattern 12 5) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 5) else d1 (change pattern 12 5)) = d11 pattern
  rw [s4895, s4886]
  rfl
theorem s4901 (pattern : Twelve) : d19 (change pattern 12 5) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 5) else d10 (change pattern 12 5)) = d19 pattern
  rw [s4900, s4899]
  rfl
theorem s4902 (pattern : Twelve) : d6 (change pattern 12 5) = d6 pattern := by
  rfl
theorem s4903 (pattern : Twelve) : d29 (change pattern 12 5) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d19 (change pattern 12 5)) = d29 pattern
  rw [s4902, s4901]
  rfl
theorem s4904 (pattern : Twelve) : d51 (change pattern 12 5) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 12 5) else d28 (change pattern 12 5)) = d51 pattern
  rw [s4903, s4898]
  rfl
theorem s4905 (pattern : Twelve) : d73 (change pattern 12 5) = d51 pattern := by
  change d51 (change pattern 12 5) = d51 pattern
  exact s4904 pattern
theorem s4906 (pattern : Twelve) : d91 (change pattern 12 5) = d3161 pattern := by
  change (if pattern.e then d73 (change pattern 12 5) else d72 (change pattern 12 5)) = d3161 pattern
  rw [s4905, s4892]
  rfl
theorem s4907 (pattern : Twelve) : d30 (change pattern 12 5) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 5) else d0 (change pattern 12 5)) = d30 pattern
  rw [s4893, s4885]
  rfl
theorem s4908 (pattern : Twelve) : d4 (change pattern 12 5) = d4 pattern := by
  rfl
theorem s4909 (pattern : Twelve) : d13 (change pattern 12 5) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 5) else d4 (change pattern 12 5)) = d13 pattern
  rw [s4902, s4908]
  rfl
theorem s4910 (pattern : Twelve) : d5 (change pattern 12 5) = d5 pattern := by
  rfl
theorem s4911 (pattern : Twelve) : d14 (change pattern 12 5) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 5) else d5 (change pattern 12 5)) = d14 pattern
  rw [s4902, s4910]
  rfl
theorem s4912 (pattern : Twelve) : d21 (change pattern 12 5) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 5) else d13 (change pattern 12 5)) = d21 pattern
  rw [s4911, s4909]
  rfl
theorem s4913 (pattern : Twelve) : d32 (change pattern 12 5) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 12 5) else d17 (change pattern 12 5)) = d32 pattern
  rw [s4912, s4889]
  rfl
theorem s4914 (pattern : Twelve) : d53 (change pattern 12 5) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 12 5) else d30 (change pattern 12 5)) = d53 pattern
  rw [s4913, s4907]
  rfl
theorem s4915 (pattern : Twelve) : d74 (change pattern 12 5) = d53 pattern := by
  change d53 (change pattern 12 5) = d53 pattern
  exact s4914 pattern
theorem s4916 (pattern : Twelve) : d23 (change pattern 12 5) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 5) else d2 (change pattern 12 5)) = d23 pattern
  rw [s4896, s4893]
  rfl
theorem s4917 (pattern : Twelve) : d34 (change pattern 12 5) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 5) else d17 (change pattern 12 5)) = d34 pattern
  rw [s4916, s4889]
  rfl
theorem s4918 (pattern : Twelve) : d55 (change pattern 12 5) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 5) else d34 (change pattern 12 5)) = d55 pattern
  rw [s4903, s4917]
  rfl
theorem s4919 (pattern : Twelve) : d75 (change pattern 12 5) = d55 pattern := by
  change d55 (change pattern 12 5) = d55 pattern
  exact s4918 pattern
theorem s4920 (pattern : Twelve) : d92 (change pattern 12 5) = d3162 pattern := by
  change (if pattern.e then d75 (change pattern 12 5) else d74 (change pattern 12 5)) = d3162 pattern
  rw [s4919, s4915]
  rfl
theorem s4921 (pattern : Twelve) : d102 (change pattern 12 5) = d3163 pattern := by
  change (if pattern.j then d92 (change pattern 12 5) else d91 (change pattern 12 5)) = d3163 pattern
  rw [s4920, s4906]
  rfl
theorem s4922 (pattern : Twelve) : d76 (change pattern 12 5) = d55 pattern := by
  change d55 (change pattern 12 5) = d55 pattern
  exact s4918 pattern
theorem s4923 (pattern : Twelve) : d93 (change pattern 12 5) = d3164 pattern := by
  change (if pattern.e then d76 (change pattern 12 5) else d72 (change pattern 12 5)) = d3164 pattern
  rw [s4922, s4892]
  rfl
theorem s4924 (pattern : Twelve) : d36 (change pattern 12 5) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d17 (change pattern 12 5)) = d36 pattern
  rw [s4902, s4889]
  rfl
theorem s4925 (pattern : Twelve) : d57 (change pattern 12 5) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 12 5) else d30 (change pattern 12 5)) = d57 pattern
  rw [s4924, s4907]
  rfl
theorem s4926 (pattern : Twelve) : d77 (change pattern 12 5) = d57 pattern := by
  change d57 (change pattern 12 5) = d57 pattern
  exact s4925 pattern
theorem s4927 (pattern : Twelve) : d78 (change pattern 12 5) = d55 pattern := by
  change d55 (change pattern 12 5) = d55 pattern
  exact s4918 pattern
theorem s4928 (pattern : Twelve) : d94 (change pattern 12 5) = d3165 pattern := by
  change (if pattern.e then d78 (change pattern 12 5) else d77 (change pattern 12 5)) = d3165 pattern
  rw [s4927, s4926]
  rfl
theorem s4929 (pattern : Twelve) : d103 (change pattern 12 5) = d3166 pattern := by
  change (if pattern.j then d94 (change pattern 12 5) else d93 (change pattern 12 5)) = d3166 pattern
  rw [s4928, s4923]
  rfl
theorem s4930 (pattern : Twelve) : d110 (change pattern 12 5) = d3167 pattern := by
  change (if pattern.d then d103 (change pattern 12 5) else d102 (change pattern 12 5)) = d3167 pattern
  rw [s4929, s4921]
  rfl
theorem s4931 (pattern : Twelve) : d37 (change pattern 12 5) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 12 5) else d17 (change pattern 12 5)) = d37 pattern
  rw [s4895, s4889]
  rfl
theorem s4932 (pattern : Twelve) : d58 (change pattern 12 5) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 12 5) else d30 (change pattern 12 5)) = d58 pattern
  rw [s4931, s4907]
  rfl
theorem s4933 (pattern : Twelve) : d79 (change pattern 12 5) = d58 pattern := by
  change d58 (change pattern 12 5) = d58 pattern
  exact s4932 pattern
theorem s4934 (pattern : Twelve) : d80 (change pattern 12 5) = d55 pattern := by
  change d55 (change pattern 12 5) = d55 pattern
  exact s4918 pattern
theorem s4935 (pattern : Twelve) : d95 (change pattern 12 5) = d3168 pattern := by
  change (if pattern.e then d80 (change pattern 12 5) else d79 (change pattern 12 5)) = d3168 pattern
  rw [s4934, s4933]
  rfl
theorem s4936 (pattern : Twelve) : d38 (change pattern 12 5) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 5) else d2 (change pattern 12 5)) = d38 pattern
  rw [s4908, s4893]
  rfl
theorem s4937 (pattern : Twelve) : d40 (change pattern 12 5) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d23 (change pattern 12 5)) = d40 pattern
  rw [s4902, s4916]
  rfl
theorem s4938 (pattern : Twelve) : d60 (change pattern 12 5) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 12 5) else d38 (change pattern 12 5)) = d60 pattern
  rw [s4937, s4936]
  rfl
theorem s4939 (pattern : Twelve) : d81 (change pattern 12 5) = d60 pattern := by
  change d60 (change pattern 12 5) = d60 pattern
  exact s4938 pattern
theorem s4940 (pattern : Twelve) : d15 (change pattern 12 5) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 5) else d4 (change pattern 12 5)) = d15 pattern
  rw [s4910, s4908]
  rfl
theorem s4941 (pattern : Twelve) : d24 (change pattern 12 5) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 5) else d4 (change pattern 12 5)) = d24 pattern
  rw [s4940, s4908]
  rfl
theorem s4942 (pattern : Twelve) : d41 (change pattern 12 5) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 12 5) else d23 (change pattern 12 5)) = d41 pattern
  rw [s4941, s4916]
  rfl
theorem s4943 (pattern : Twelve) : d16 (change pattern 12 5) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 5) else d2 (change pattern 12 5)) = d16 pattern
  rw [s4908, s4893]
  rfl
theorem s4944 (pattern : Twelve) : d12 (change pattern 12 5) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 5) else d3 (change pattern 12 5)) = d12 pattern
  rw [s4910, s4895]
  rfl
theorem s4945 (pattern : Twelve) : d25 (change pattern 12 5) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 5) else d16 (change pattern 12 5)) = d25 pattern
  rw [s4944, s4943]
  rfl
theorem s4946 (pattern : Twelve) : d42 (change pattern 12 5) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d25 (change pattern 12 5)) = d42 pattern
  rw [s4902, s4945]
  rfl
theorem s4947 (pattern : Twelve) : d61 (change pattern 12 5) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 12 5) else d41 (change pattern 12 5)) = d61 pattern
  rw [s4946, s4942]
  rfl
theorem s4948 (pattern : Twelve) : d82 (change pattern 12 5) = d61 pattern := by
  change d61 (change pattern 12 5) = d61 pattern
  exact s4947 pattern
theorem s4949 (pattern : Twelve) : d96 (change pattern 12 5) = d3169 pattern := by
  change (if pattern.e then d82 (change pattern 12 5) else d81 (change pattern 12 5)) = d3169 pattern
  rw [s4948, s4939]
  rfl
end NetHack.Sokoban21.Diagram
