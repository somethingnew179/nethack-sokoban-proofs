/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions30
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4650 (pattern : Twelve) : d150 (change pattern 12 8) = d3065 pattern := by
  change (if pattern.j then d146 (change pattern 12 8) else d144 (change pattern 12 8)) = d3065 pattern
  rw [s4649, s4641]
  rfl
theorem s4651 (pattern : Twelve) : d153 (change pattern 12 8) = d3066 pattern := by
  change (if pattern.d then d150 (change pattern 12 8) else d149 (change pattern 12 8)) = d3066 pattern
  rw [s4650, s4647]
  rfl
theorem s4652 (pattern : Twelve) : d122 (change pattern 12 8) = d4 pattern := by
  change d4 (change pattern 12 8) = d4 pattern
  exact s4584 pattern
theorem s4653 (pattern : Twelve) : d131 (change pattern 12 8) = d3067 pattern := by
  change (if pattern.h then d122 (change pattern 12 8) else d121 (change pattern 12 8)) = d3067 pattern
  rw [s4652, s4642]
  rfl
theorem s4654 (pattern : Twelve) : d140 (change pattern 12 8) = d3068 pattern := by
  change (if pattern.f then d131 (change pattern 12 8) else d30 (change pattern 12 8)) = d3068 pattern
  rw [s4653, s4581]
  rfl
theorem s4655 (pattern : Twelve) : d123 (change pattern 12 8) = d3 pattern := by
  change d3 (change pattern 12 8) = d3 pattern
  exact s4572 pattern
theorem s4656 (pattern : Twelve) : d132 (change pattern 12 8) = d2427 pattern := by
  change (if pattern.h then d123 (change pattern 12 8) else d30 (change pattern 12 8)) = d2427 pattern
  rw [s4655, s4581]
  rfl
theorem s4657 (pattern : Twelve) : d141 (change pattern 12 8) = d3069 pattern := by
  change (if pattern.f then d129 (change pattern 12 8) else d132 (change pattern 12 8)) = d3069 pattern
  rw [s4639, s4656]
  rfl
theorem s4658 (pattern : Twelve) : d147 (change pattern 12 8) = d3070 pattern := by
  change (if pattern.e then d141 (change pattern 12 8) else d140 (change pattern 12 8)) = d3070 pattern
  rw [s4657, s4654]
  rfl
theorem s4659 (pattern : Twelve) : d118 (change pattern 12 8) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 8) else d5 (change pattern 12 8)) = d118 pattern
  rw [s4589, s4582]
  rfl
theorem s4660 (pattern : Twelve) : d124 (change pattern 12 8) = d118 pattern := by
  change d118 (change pattern 12 8) = d118 pattern
  exact s4659 pattern
theorem s4661 (pattern : Twelve) : d125 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4662 (pattern : Twelve) : d133 (change pattern 12 8) = d3071 pattern := by
  change (if pattern.h then d125 (change pattern 12 8) else d124 (change pattern 12 8)) = d3071 pattern
  rw [s4661, s4660]
  rfl
theorem s4663 (pattern : Twelve) : d142 (change pattern 12 8) = d3072 pattern := by
  change (if pattern.f then d133 (change pattern 12 8) else d59 (change pattern 12 8)) = d3072 pattern
  rw [s4662, s4621]
  rfl
theorem s4664 (pattern : Twelve) : d126 (change pattern 12 8) = d5 pattern := by
  change d5 (change pattern 12 8) = d5 pattern
  exact s4582 pattern
theorem s4665 (pattern : Twelve) : d47 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4666 (pattern : Twelve) : d134 (change pattern 12 8) = d3073 pattern := by
  change (if pattern.h then d47 (change pattern 12 8) else d126 (change pattern 12 8)) = d3073 pattern
  rw [s4665, s4664]
  rfl
theorem s4667 (pattern : Twelve) : d127 (change pattern 12 8) = d22 pattern := by
  change d22 (change pattern 12 8) = d22 pattern
  exact s4594 pattern
theorem s4668 (pattern : Twelve) : d128 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4669 (pattern : Twelve) : d135 (change pattern 12 8) = d3074 pattern := by
  change (if pattern.h then d128 (change pattern 12 8) else d127 (change pattern 12 8)) = d3074 pattern
  rw [s4668, s4667]
  rfl
theorem s4670 (pattern : Twelve) : d143 (change pattern 12 8) = d3075 pattern := by
  change (if pattern.f then d135 (change pattern 12 8) else d134 (change pattern 12 8)) = d3075 pattern
  rw [s4669, s4666]
  rfl
theorem s4671 (pattern : Twelve) : d148 (change pattern 12 8) = d3076 pattern := by
  change (if pattern.e then d143 (change pattern 12 8) else d142 (change pattern 12 8)) = d3076 pattern
  rw [s4670, s4663]
  rfl
theorem s4672 (pattern : Twelve) : d151 (change pattern 12 8) = d3077 pattern := by
  change (if pattern.j then d148 (change pattern 12 8) else d147 (change pattern 12 8)) = d3077 pattern
  rw [s4671, s4658]
  rfl
theorem s4673 (pattern : Twelve) : d152 (change pattern 12 8) = d3078 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d146 (change pattern 12 8)) = d3078 pattern
  rw [s4576, s4649]
  rfl
theorem s4674 (pattern : Twelve) : d154 (change pattern 12 8) = d3079 pattern := by
  change (if pattern.d then d152 (change pattern 12 8) else d151 (change pattern 12 8)) = d3079 pattern
  rw [s4673, s4672]
  rfl
theorem s4675 (pattern : Twelve) : d155 (change pattern 12 8) = d3080 pattern := by
  change (if pattern.c then d154 (change pattern 12 8) else d153 (change pattern 12 8)) = d3080 pattern
  rw [s4674, s4651]
  rfl
theorem s4676 (pattern : Twelve) : d156 (change pattern 12 8) = d3081 pattern := by
  change (if pattern.a then d155 (change pattern 12 8) else d114 (change pattern 12 8)) = d3081 pattern
  rw [s4675, s4635]
  rfl
theorem s4677 (pattern : Twelve) : d816 (change pattern 12 8) = d1 pattern := by
  change d1 (change pattern 12 8) = d1 pattern
  exact s4565 pattern
theorem s4678 (pattern : Twelve) : d824 (change pattern 12 8) = d1 pattern := by
  change (if pattern.h then d816 (change pattern 12 8) else d27 (change pattern 12 8)) = d1 pattern
  rw [s4677, s4567]
  simp only [ite_self]
theorem s4679 (pattern : Twelve) : d838 (change pattern 12 8) = d1859 pattern := by
  change (if pattern.f then d824 (change pattern 12 8) else d0 (change pattern 12 8)) = d1859 pattern
  rw [s4678, s4564]
  rfl
theorem s4680 (pattern : Twelve) : d7 (change pattern 12 8) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 8) else d0 (change pattern 12 8)) = d7 pattern
  rw [s4565, s4564]
  rfl
theorem s4681 (pattern : Twelve) : d17 (change pattern 12 8) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 8) else d0 (change pattern 12 8)) = d17 pattern
  rw [s4680, s4564]
  rfl
theorem s4682 (pattern : Twelve) : d817 (change pattern 12 8) = d25 pattern := by
  change d25 (change pattern 12 8) = d25 pattern
  exact s4637 pattern
theorem s4683 (pattern : Twelve) : d825 (change pattern 12 8) = d1690 pattern := by
  change (if pattern.h then d42 (change pattern 12 8) else d817 (change pattern 12 8)) = d1690 pattern
  rw [s4628, s4682]
  rfl
theorem s4684 (pattern : Twelve) : d839 (change pattern 12 8) = d2291 pattern := by
  change (if pattern.f then d825 (change pattern 12 8) else d17 (change pattern 12 8)) = d2291 pattern
  rw [s4683, s4681]
  rfl
theorem s4685 (pattern : Twelve) : d853 (change pattern 12 8) = d2292 pattern := by
  change (if pattern.e then d839 (change pattern 12 8) else d838 (change pattern 12 8)) = d2292 pattern
  rw [s4684, s4679]
  rfl
theorem s4686 (pattern : Twelve) : d818 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4687 (pattern : Twelve) : d826 (change pattern 12 8) = d2284 pattern := by
  change (if pattern.h then d818 (change pattern 12 8) else d34 (change pattern 12 8)) = d2284 pattern
  rw [s4686, s4598]
  rfl
theorem s4688 (pattern : Twelve) : d840 (change pattern 12 8) = d3044 pattern := by
  change (if pattern.f then d826 (change pattern 12 8) else d56 (change pattern 12 8)) = d3044 pattern
  rw [s4687, s4606]
  rfl
theorem s4689 (pattern : Twelve) : d827 (change pattern 12 8) = d2284 pattern := by
  change (if pattern.h then d36 (change pattern 12 8) else d34 (change pattern 12 8)) = d2284 pattern
  rw [s4607, s4598]
  rfl
theorem s4690 (pattern : Twelve) : d841 (change pattern 12 8) = d3082 pattern := by
  change (if pattern.f then d825 (change pattern 12 8) else d827 (change pattern 12 8)) = d3082 pattern
  rw [s4683, s4689]
  rfl
theorem s4691 (pattern : Twelve) : d854 (change pattern 12 8) = d3083 pattern := by
  change (if pattern.e then d841 (change pattern 12 8) else d840 (change pattern 12 8)) = d3083 pattern
  rw [s4690, s4688]
  rfl
theorem s4692 (pattern : Twelve) : d861 (change pattern 12 8) = d3084 pattern := by
  change (if pattern.j then d854 (change pattern 12 8) else d853 (change pattern 12 8)) = d3084 pattern
  rw [s4691, s4685]
  rfl
theorem s4693 (pattern : Twelve) : d819 (change pattern 12 8) = d3 pattern := by
  change d3 (change pattern 12 8) = d3 pattern
  exact s4572 pattern
theorem s4694 (pattern : Twelve) : d828 (change pattern 12 8) = d3085 pattern := by
  change (if pattern.h then d819 (change pattern 12 8) else d34 (change pattern 12 8)) = d3085 pattern
  rw [s4693, s4598]
  rfl
theorem s4695 (pattern : Twelve) : d842 (change pattern 12 8) = d3086 pattern := by
  change (if pattern.f then d828 (change pattern 12 8) else d30 (change pattern 12 8)) = d3086 pattern
  rw [s4694, s4581]
  rfl
theorem s4696 (pattern : Twelve) : d843 (change pattern 12 8) = d3087 pattern := by
  change (if pattern.f then d825 (change pattern 12 8) else d34 (change pattern 12 8)) = d3087 pattern
  rw [s4683, s4598]
  rfl
theorem s4697 (pattern : Twelve) : d855 (change pattern 12 8) = d3088 pattern := by
  change (if pattern.e then d843 (change pattern 12 8) else d842 (change pattern 12 8)) = d3088 pattern
  rw [s4696, s4695]
  rfl
theorem s4698 (pattern : Twelve) : d820 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4699 (pattern : Twelve) : d829 (change pattern 12 8) = d3051 pattern := by
  change (if pattern.h then d820 (change pattern 12 8) else d41 (change pattern 12 8)) = d3051 pattern
  rw [s4698, s4627]
  rfl
theorem s4700 (pattern : Twelve) : d844 (change pattern 12 8) = d3052 pattern := by
  change (if pattern.f then d829 (change pattern 12 8) else d59 (change pattern 12 8)) = d3052 pattern
  rw [s4699, s4621]
  rfl
theorem s4701 (pattern : Twelve) : d830 (change pattern 12 8) = d3051 pattern := by
  change (if pattern.h then d40 (change pattern 12 8) else d41 (change pattern 12 8)) = d3051 pattern
  rw [s4622, s4627]
  rfl
theorem s4702 (pattern : Twelve) : d821 (change pattern 12 8) = d21 pattern := by
  change d21 (change pattern 12 8) = d21 pattern
  exact s4590 pattern
theorem s4703 (pattern : Twelve) : d822 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4704 (pattern : Twelve) : d831 (change pattern 12 8) = d2469 pattern := by
  change (if pattern.h then d822 (change pattern 12 8) else d821 (change pattern 12 8)) = d2469 pattern
  rw [s4703, s4702]
  rfl
theorem s4705 (pattern : Twelve) : d845 (change pattern 12 8) = d3089 pattern := by
  change (if pattern.f then d831 (change pattern 12 8) else d830 (change pattern 12 8)) = d3089 pattern
  rw [s4704, s4701]
  rfl
theorem s4706 (pattern : Twelve) : d856 (change pattern 12 8) = d3090 pattern := by
  change (if pattern.e then d845 (change pattern 12 8) else d844 (change pattern 12 8)) = d3090 pattern
  rw [s4705, s4700]
  rfl
theorem s4707 (pattern : Twelve) : d862 (change pattern 12 8) = d3091 pattern := by
  change (if pattern.j then d856 (change pattern 12 8) else d855 (change pattern 12 8)) = d3091 pattern
  rw [s4706, s4697]
  rfl
theorem s4708 (pattern : Twelve) : d863 (change pattern 12 8) = d3092 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d854 (change pattern 12 8)) = d3092 pattern
  rw [s4576, s4691]
  rfl
theorem s4709 (pattern : Twelve) : d867 (change pattern 12 8) = d3093 pattern := by
  change (if pattern.d then d863 (change pattern 12 8) else d862 (change pattern 12 8)) = d3093 pattern
  rw [s4708, s4707]
  rfl
theorem s4710 (pattern : Twelve) : d869 (change pattern 12 8) = d3094 pattern := by
  change (if pattern.c then d867 (change pattern 12 8) else d861 (change pattern 12 8)) = d3094 pattern
  rw [s4709, s4692]
  rfl
theorem s4711 (pattern : Twelve) : d872 (change pattern 12 8) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 8) else d1 (change pattern 12 8)) = d872 pattern
  rw [s4571, s4565]
  rfl
theorem s4712 (pattern : Twelve) : d874 (change pattern 12 8) = d872 pattern := by
  change d872 (change pattern 12 8) = d872 pattern
  exact s4711 pattern
theorem s4713 (pattern : Twelve) : d875 (change pattern 12 8) = d872 pattern := by
  change d872 (change pattern 12 8) = d872 pattern
  exact s4711 pattern
theorem s4714 (pattern : Twelve) : d882 (change pattern 12 8) = d872 pattern := by
  change (if pattern.h then d875 (change pattern 12 8) else d874 (change pattern 12 8)) = d872 pattern
  rw [s4713, s4712]
  simp only [ite_self]
theorem s4715 (pattern : Twelve) : d890 (change pattern 12 8) = d3095 pattern := by
  change (if pattern.f then d882 (change pattern 12 8) else d0 (change pattern 12 8)) = d3095 pattern
  rw [s4714, s4564]
  rfl
theorem s4716 (pattern : Twelve) : d876 (change pattern 12 8) = d21 pattern := by
  change d21 (change pattern 12 8) = d21 pattern
  exact s4590 pattern
theorem s4717 (pattern : Twelve) : d883 (change pattern 12 8) = d2469 pattern := by
  change (if pattern.h then d42 (change pattern 12 8) else d876 (change pattern 12 8)) = d2469 pattern
  rw [s4628, s4716]
  rfl
theorem s4718 (pattern : Twelve) : d891 (change pattern 12 8) = d3096 pattern := by
  change (if pattern.f then d883 (change pattern 12 8) else d17 (change pattern 12 8)) = d3096 pattern
  rw [s4717, s4681]
  rfl
theorem s4719 (pattern : Twelve) : d898 (change pattern 12 8) = d3097 pattern := by
  change (if pattern.e then d891 (change pattern 12 8) else d890 (change pattern 12 8)) = d3097 pattern
  rw [s4718, s4715]
  rfl
theorem s4720 (pattern : Twelve) : d815 (change pattern 12 8) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 8) else d9 (change pattern 12 8)) = d815 pattern
  rw [s4572, s4573]
  rfl
theorem s4721 (pattern : Twelve) : d877 (change pattern 12 8) = d815 pattern := by
  change d815 (change pattern 12 8) = d815 pattern
  exact s4720 pattern
theorem s4722 (pattern : Twelve) : d884 (change pattern 12 8) = d3098 pattern := by
  change (if pattern.h then d818 (change pattern 12 8) else d877 (change pattern 12 8)) = d3098 pattern
  rw [s4686, s4721]
  rfl
theorem s4723 (pattern : Twelve) : d892 (change pattern 12 8) = d3099 pattern := by
  change (if pattern.f then d884 (change pattern 12 8) else d56 (change pattern 12 8)) = d3099 pattern
  rw [s4722, s4606]
  rfl
theorem s4724 (pattern : Twelve) : d893 (change pattern 12 8) = d3100 pattern := by
  change (if pattern.f then d883 (change pattern 12 8) else d827 (change pattern 12 8)) = d3100 pattern
  rw [s4717, s4689]
  rfl
theorem s4725 (pattern : Twelve) : d899 (change pattern 12 8) = d3101 pattern := by
  change (if pattern.e then d893 (change pattern 12 8) else d892 (change pattern 12 8)) = d3101 pattern
  rw [s4724, s4723]
  rfl
theorem s4726 (pattern : Twelve) : d902 (change pattern 12 8) = d3102 pattern := by
  change (if pattern.j then d899 (change pattern 12 8) else d898 (change pattern 12 8)) = d3102 pattern
  rw [s4725, s4719]
  rfl
theorem s4727 (pattern : Twelve) : d878 (change pattern 12 8) = d24 pattern := by
  change d24 (change pattern 12 8) = d24 pattern
  exact s4626 pattern
theorem s4728 (pattern : Twelve) : d885 (change pattern 12 8) = d3103 pattern := by
  change (if pattern.h then d878 (change pattern 12 8) else d877 (change pattern 12 8)) = d3103 pattern
  rw [s4727, s4721]
  rfl
theorem s4729 (pattern : Twelve) : d894 (change pattern 12 8) = d3104 pattern := by
  change (if pattern.f then d885 (change pattern 12 8) else d30 (change pattern 12 8)) = d3104 pattern
  rw [s4728, s4581]
  rfl
theorem s4730 (pattern : Twelve) : d117 (change pattern 12 8) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 8) else d3 (change pattern 12 8)) = d117 pattern
  rw [s4584, s4572]
  rfl
theorem s4731 (pattern : Twelve) : d119 (change pattern 12 8) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 8) else d3 (change pattern 12 8)) = d119 pattern
  rw [s4730, s4572]
  rfl
theorem s4732 (pattern : Twelve) : d879 (change pattern 12 8) = d119 pattern := by
  change d119 (change pattern 12 8) = d119 pattern
  exact s4731 pattern
theorem s4733 (pattern : Twelve) : d886 (change pattern 12 8) = d2445 pattern := by
  change (if pattern.h then d879 (change pattern 12 8) else d34 (change pattern 12 8)) = d2445 pattern
  rw [s4732, s4598]
  rfl
theorem s4734 (pattern : Twelve) : d895 (change pattern 12 8) = d3105 pattern := by
  change (if pattern.f then d883 (change pattern 12 8) else d886 (change pattern 12 8)) = d3105 pattern
  rw [s4717, s4733]
  rfl
theorem s4735 (pattern : Twelve) : d900 (change pattern 12 8) = d3106 pattern := by
  change (if pattern.e then d895 (change pattern 12 8) else d894 (change pattern 12 8)) = d3106 pattern
  rw [s4734, s4729]
  rfl
theorem s4736 (pattern : Twelve) : d880 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4737 (pattern : Twelve) : d887 (change pattern 12 8) = d3074 pattern := by
  change (if pattern.h then d880 (change pattern 12 8) else d127 (change pattern 12 8)) = d3074 pattern
  rw [s4736, s4667]
  rfl
theorem s4738 (pattern : Twelve) : d896 (change pattern 12 8) = d3107 pattern := by
  change (if pattern.f then d887 (change pattern 12 8) else d59 (change pattern 12 8)) = d3107 pattern
  rw [s4737, s4621]
  rfl
theorem s4739 (pattern : Twelve) : d881 (change pattern 12 8) = d118 pattern := by
  change d118 (change pattern 12 8) = d118 pattern
  exact s4659 pattern
theorem s4740 (pattern : Twelve) : d888 (change pattern 12 8) = d3071 pattern := by
  change (if pattern.h then d125 (change pattern 12 8) else d881 (change pattern 12 8)) = d3071 pattern
  rw [s4661, s4739]
  rfl
theorem s4741 (pattern : Twelve) : d889 (change pattern 12 8) = d6 pattern := by
  change (if pattern.h then d6 (change pattern 12 8) else d42 (change pattern 12 8)) = d6 pattern
  rw [s4576, s4628]
  simp only [ite_self]
theorem s4742 (pattern : Twelve) : d897 (change pattern 12 8) = d3108 pattern := by
  change (if pattern.f then d889 (change pattern 12 8) else d888 (change pattern 12 8)) = d3108 pattern
  rw [s4741, s4740]
  rfl
theorem s4743 (pattern : Twelve) : d901 (change pattern 12 8) = d3109 pattern := by
  change (if pattern.e then d897 (change pattern 12 8) else d896 (change pattern 12 8)) = d3109 pattern
  rw [s4742, s4738]
  rfl
theorem s4744 (pattern : Twelve) : d903 (change pattern 12 8) = d3110 pattern := by
  change (if pattern.j then d901 (change pattern 12 8) else d900 (change pattern 12 8)) = d3110 pattern
  rw [s4743, s4735]
  rfl
theorem s4745 (pattern : Twelve) : d904 (change pattern 12 8) = d3111 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d899 (change pattern 12 8)) = d3111 pattern
  rw [s4576, s4725]
  rfl
theorem s4746 (pattern : Twelve) : d905 (change pattern 12 8) = d3112 pattern := by
  change (if pattern.d then d904 (change pattern 12 8) else d903 (change pattern 12 8)) = d3112 pattern
  rw [s4745, s4744]
  rfl
theorem s4747 (pattern : Twelve) : d906 (change pattern 12 8) = d3113 pattern := by
  change (if pattern.c then d905 (change pattern 12 8) else d902 (change pattern 12 8)) = d3113 pattern
  rw [s4746, s4726]
  rfl
theorem s4748 (pattern : Twelve) : d907 (change pattern 12 8) = d3114 pattern := by
  change (if pattern.a then d906 (change pattern 12 8) else d869 (change pattern 12 8)) = d3114 pattern
  rw [s4747, s4710]
  rfl
theorem s4749 (pattern : Twelve) : d1278 (change pattern 12 8) = d872 pattern := by
  change d872 (change pattern 12 8) = d872 pattern
  exact s4711 pattern
theorem s4750 (pattern : Twelve) : d1284 (change pattern 12 8) = d872 pattern := by
  change (if pattern.h then d872 (change pattern 12 8) else d1278 (change pattern 12 8)) = d872 pattern
  rw [s4711, s4749]
  simp only [ite_self]
theorem s4751 (pattern : Twelve) : d1293 (change pattern 12 8) = d1976 pattern := by
  change (if pattern.f then d1284 (change pattern 12 8) else d17 (change pattern 12 8)) = d1976 pattern
  rw [s4750, s4681]
  rfl
theorem s4752 (pattern : Twelve) : d10 (change pattern 12 8) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 8) else d0 (change pattern 12 8)) = d10 pattern
  rw [s4570, s4564]
  rfl
theorem s4753 (pattern : Twelve) : d11 (change pattern 12 8) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 8) else d1 (change pattern 12 8)) = d11 pattern
  rw [s4572, s4565]
  rfl
theorem s4754 (pattern : Twelve) : d19 (change pattern 12 8) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 8) else d10 (change pattern 12 8)) = d19 pattern
  rw [s4753, s4752]
  rfl
theorem s4755 (pattern : Twelve) : d1294 (change pattern 12 8) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d19 (change pattern 12 8)) = d1294 pattern
  rw [s4576, s4754]
  rfl
theorem s4756 (pattern : Twelve) : d1305 (change pattern 12 8) = d1977 pattern := by
  change (if pattern.e then d1294 (change pattern 12 8) else d1293 (change pattern 12 8)) = d1977 pattern
  rw [s4755, s4751]
  rfl
theorem s4757 (pattern : Twelve) : d1276 (change pattern 12 8) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 8) else d9 (change pattern 12 8)) = d1276 pattern
  rw [s4730, s4573]
  rfl
theorem s4758 (pattern : Twelve) : d1279 (change pattern 12 8) = d1276 pattern := by
  change d1276 (change pattern 12 8) = d1276 pattern
  exact s4757 pattern
theorem s4759 (pattern : Twelve) : d1280 (change pattern 12 8) = d6 pattern := by
  change d6 (change pattern 12 8) = d6 pattern
  exact s4576 pattern
theorem s4760 (pattern : Twelve) : d1285 (change pattern 12 8) = d3115 pattern := by
  change (if pattern.h then d1280 (change pattern 12 8) else d1279 (change pattern 12 8)) = d3115 pattern
  rw [s4759, s4758]
  rfl
theorem s4761 (pattern : Twelve) : d1295 (change pattern 12 8) = d3116 pattern := by
  change (if pattern.f then d1285 (change pattern 12 8) else d827 (change pattern 12 8)) = d3116 pattern
  rw [s4760, s4689]
  rfl
theorem s4762 (pattern : Twelve) : d1286 (change pattern 12 8) = d1690 pattern := by
  change (if pattern.h then d29 (change pattern 12 8) else d817 (change pattern 12 8)) = d1690 pattern
  rw [s4577, s4682]
  rfl
theorem s4763 (pattern : Twelve) : d1296 (change pattern 12 8) = d1694 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d1286 (change pattern 12 8)) = d1694 pattern
  rw [s4576, s4762]
  rfl
theorem s4764 (pattern : Twelve) : d1306 (change pattern 12 8) = d3117 pattern := by
  change (if pattern.e then d1296 (change pattern 12 8) else d1295 (change pattern 12 8)) = d3117 pattern
  rw [s4763, s4761]
  rfl
theorem s4765 (pattern : Twelve) : d1313 (change pattern 12 8) = d3118 pattern := by
  change (if pattern.j then d1306 (change pattern 12 8) else d1305 (change pattern 12 8)) = d3118 pattern
  rw [s4764, s4756]
  rfl
theorem s4766 (pattern : Twelve) : d1281 (change pattern 12 8) = d119 pattern := by
  change d119 (change pattern 12 8) = d119 pattern
  exact s4731 pattern
theorem s4767 (pattern : Twelve) : d1287 (change pattern 12 8) = d2392 pattern := by
  change (if pattern.h then d1281 (change pattern 12 8) else d1279 (change pattern 12 8)) = d2392 pattern
  rw [s4766, s4758]
  rfl
theorem s4768 (pattern : Twelve) : d1297 (change pattern 12 8) = d2454 pattern := by
  change (if pattern.f then d1287 (change pattern 12 8) else d34 (change pattern 12 8)) = d2454 pattern
  rw [s4767, s4598]
  rfl
theorem s4769 (pattern : Twelve) : d1298 (change pattern 12 8) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d817 (change pattern 12 8)) = d1650 pattern
  rw [s4576, s4682]
  rfl
theorem s4770 (pattern : Twelve) : d1307 (change pattern 12 8) = d2455 pattern := by
  change (if pattern.e then d1298 (change pattern 12 8) else d1297 (change pattern 12 8)) = d2455 pattern
  rw [s4769, s4768]
  rfl
theorem s4771 (pattern : Twelve) : d1277 (change pattern 12 8) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 8) else d15 (change pattern 12 8)) = d1277 pattern
  rw [s4589, s4625]
  rfl
theorem s4772 (pattern : Twelve) : d1282 (change pattern 12 8) = d1277 pattern := by
  change d1277 (change pattern 12 8) = d1277 pattern
  exact s4771 pattern
theorem s4773 (pattern : Twelve) : d1288 (change pattern 12 8) = d3119 pattern := by
  change (if pattern.h then d125 (change pattern 12 8) else d1282 (change pattern 12 8)) = d3119 pattern
  rw [s4661, s4772]
  rfl
theorem s4774 (pattern : Twelve) : d1299 (change pattern 12 8) = d3120 pattern := by
  change (if pattern.f then d1288 (change pattern 12 8) else d830 (change pattern 12 8)) = d3120 pattern
  rw [s4773, s4701]
  rfl
theorem s4775 (pattern : Twelve) : d1289 (change pattern 12 8) = d2469 pattern := by
  change (if pattern.h then d42 (change pattern 12 8) else d821 (change pattern 12 8)) = d2469 pattern
  rw [s4628, s4702]
  rfl
theorem s4776 (pattern : Twelve) : d1300 (change pattern 12 8) = d2470 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d1289 (change pattern 12 8)) = d2470 pattern
  rw [s4576, s4775]
  rfl
theorem s4777 (pattern : Twelve) : d1308 (change pattern 12 8) = d3121 pattern := by
  change (if pattern.e then d1300 (change pattern 12 8) else d1299 (change pattern 12 8)) = d3121 pattern
  rw [s4776, s4774]
  rfl
theorem s4778 (pattern : Twelve) : d1314 (change pattern 12 8) = d3122 pattern := by
  change (if pattern.j then d1308 (change pattern 12 8) else d1307 (change pattern 12 8)) = d3122 pattern
  rw [s4777, s4770]
  rfl
theorem s4779 (pattern : Twelve) : d1315 (change pattern 12 8) = d3123 pattern := by
  change (if pattern.j then d6 (change pattern 12 8) else d1306 (change pattern 12 8)) = d3123 pattern
  rw [s4576, s4764]
  rfl
theorem s4780 (pattern : Twelve) : d1319 (change pattern 12 8) = d3124 pattern := by
  change (if pattern.d then d1315 (change pattern 12 8) else d1314 (change pattern 12 8)) = d3124 pattern
  rw [s4779, s4778]
  rfl
theorem s4781 (pattern : Twelve) : d1321 (change pattern 12 8) = d3125 pattern := by
  change (if pattern.c then d1319 (change pattern 12 8) else d1313 (change pattern 12 8)) = d3125 pattern
  rw [s4780, s4765]
  rfl
theorem s4782 (pattern : Twelve) : d1324 (change pattern 12 8) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 8) else d11 (change pattern 12 8)) = d1324 pattern
  rw [s4636, s4753]
  rfl
theorem s4783 (pattern : Twelve) : d1325 (change pattern 12 8) = d1324 pattern := by
  change d1324 (change pattern 12 8) = d1324 pattern
  exact s4782 pattern
theorem s4784 (pattern : Twelve) : d1326 (change pattern 12 8) = d1324 pattern := by
  change d1324 (change pattern 12 8) = d1324 pattern
  exact s4782 pattern
theorem s4785 (pattern : Twelve) : d1333 (change pattern 12 8) = d1324 pattern := by
  change (if pattern.h then d1326 (change pattern 12 8) else d1325 (change pattern 12 8)) = d1324 pattern
  rw [s4784, s4783]
  simp only [ite_self]
theorem s4786 (pattern : Twelve) : d1339 (change pattern 12 8) = d3126 pattern := by
  change (if pattern.f then d1333 (change pattern 12 8) else d17 (change pattern 12 8)) = d3126 pattern
  rw [s4785, s4681]
  rfl
theorem s4787 (pattern : Twelve) : d1345 (change pattern 12 8) = d3127 pattern := by
  change (if pattern.e then d1294 (change pattern 12 8) else d1339 (change pattern 12 8)) = d3127 pattern
  rw [s4755, s4786]
  rfl
theorem s4788 (pattern : Twelve) : d1327 (change pattern 12 8) = d119 pattern := by
  change d119 (change pattern 12 8) = d119 pattern
  exact s4731 pattern
theorem s4789 (pattern : Twelve) : d1334 (change pattern 12 8) = d3128 pattern := by
  change (if pattern.h then d1280 (change pattern 12 8) else d1327 (change pattern 12 8)) = d3128 pattern
  rw [s4759, s4788]
  rfl
theorem s4790 (pattern : Twelve) : d1340 (change pattern 12 8) = d3129 pattern := by
  change (if pattern.f then d1334 (change pattern 12 8) else d827 (change pattern 12 8)) = d3129 pattern
  rw [s4789, s4689]
  rfl
theorem s4791 (pattern : Twelve) : d1346 (change pattern 12 8) = d3130 pattern := by
  change (if pattern.e then d1296 (change pattern 12 8) else d1340 (change pattern 12 8)) = d3130 pattern
  rw [s4763, s4790]
  rfl
theorem s4792 (pattern : Twelve) : d1349 (change pattern 12 8) = d3131 pattern := by
  change (if pattern.j then d1346 (change pattern 12 8) else d1345 (change pattern 12 8)) = d3131 pattern
  rw [s4791, s4787]
  rfl
theorem s4793 (pattern : Twelve) : d1328 (change pattern 12 8) = d1277 pattern := by
  change d1277 (change pattern 12 8) = d1277 pattern
  exact s4771 pattern
theorem s4794 (pattern : Twelve) : d1335 (change pattern 12 8) = d3132 pattern := by
  change (if pattern.h then d1328 (change pattern 12 8) else d1327 (change pattern 12 8)) = d3132 pattern
  rw [s4793, s4788]
  rfl
theorem s4795 (pattern : Twelve) : d1341 (change pattern 12 8) = d3133 pattern := by
  change (if pattern.f then d1335 (change pattern 12 8) else d34 (change pattern 12 8)) = d3133 pattern
  rw [s4794, s4598]
  rfl
theorem s4796 (pattern : Twelve) : d1329 (change pattern 12 8) = d20 pattern := by
  change d20 (change pattern 12 8) = d20 pattern
  exact s4586 pattern
theorem s4797 (pattern : Twelve) : d1336 (change pattern 12 8) = d2461 pattern := by
  change (if pattern.h then d1329 (change pattern 12 8) else d817 (change pattern 12 8)) = d2461 pattern
  rw [s4796, s4682]
  rfl
theorem s4798 (pattern : Twelve) : d1342 (change pattern 12 8) = d2462 pattern := by
  change (if pattern.f then d6 (change pattern 12 8) else d1336 (change pattern 12 8)) = d2462 pattern
  rw [s4576, s4797]
  rfl
theorem s4799 (pattern : Twelve) : d1347 (change pattern 12 8) = d3134 pattern := by
  change (if pattern.e then d1342 (change pattern 12 8) else d1341 (change pattern 12 8)) = d3134 pattern
  rw [s4798, s4795]
  rfl
end NetHack.Sokoban21.Diagram
