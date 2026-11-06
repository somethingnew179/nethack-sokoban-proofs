/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions27
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4200 (pattern : Twelve) : d1789 (change pattern 11 12) = d2859 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d644 (change pattern 11 12)) = d2859 pattern
  rw [s4038, s4036]
  rfl
theorem s4201 (pattern : Twelve) : d1797 (change pattern 11 12) = d2860 pattern := by
  change (if pattern.e then d1789 (change pattern 11 12) else d1788 (change pattern 11 12)) = d2860 pattern
  rw [s4200, s4199]
  rfl
theorem s4202 (pattern : Twelve) : d1780 (change pattern 11 12) = d2861 pattern := by
  change (if pattern.i then d639 (change pattern 11 12) else d635 (change pattern 11 12)) = d2861 pattern
  rw [s4124, s4171]
  rfl
theorem s4203 (pattern : Twelve) : d1781 (change pattern 11 12) = d2862 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d635 (change pattern 11 12)) = d2862 pattern
  rw [s4038, s4171]
  rfl
theorem s4204 (pattern : Twelve) : d1784 (change pattern 11 12) = d2863 pattern := by
  change (if pattern.h then d1781 (change pattern 11 12) else d1780 (change pattern 11 12)) = d2863 pattern
  rw [s4203, s4202]
  rfl
theorem s4205 (pattern : Twelve) : d1790 (change pattern 11 12) = d2864 pattern := by
  change (if pattern.f then d1784 (change pattern 11 12) else d1566 (change pattern 11 12)) = d2864 pattern
  rw [s4204, s4146]
  rfl
theorem s4206 (pattern : Twelve) : d1798 (change pattern 11 12) = d2865 pattern := by
  change (if pattern.e then d1584 (change pattern 11 12) else d1790 (change pattern 11 12)) = d2865 pattern
  rw [s4162, s4205]
  rfl
theorem s4207 (pattern : Twelve) : d1804 (change pattern 11 12) = d2866 pattern := by
  change (if pattern.j then d1798 (change pattern 11 12) else d1797 (change pattern 11 12)) = d2866 pattern
  rw [s4206, s4201]
  rfl
theorem s4208 (pattern : Twelve) : d1791 (change pattern 11 12) = d2867 pattern := by
  change (if pattern.f then d1780 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2867 pattern
  rw [s4202, s4037]
  rfl
theorem s4209 (pattern : Twelve) : d1792 (change pattern 11 12) = d2868 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1186 (change pattern 11 12)) = d2868 pattern
  rw [s4038, s4086]
  rfl
theorem s4210 (pattern : Twelve) : d1799 (change pattern 11 12) = d2869 pattern := by
  change (if pattern.e then d1792 (change pattern 11 12) else d1791 (change pattern 11 12)) = d2869 pattern
  rw [s4209, s4208]
  rfl
theorem s4211 (pattern : Twelve) : d1782 (change pattern 11 12) = d2870 pattern := by
  change (if pattern.i then d22 (change pattern 11 12) else d639 (change pattern 11 12)) = d2870 pattern
  rw [s4122, s4124]
  rfl
theorem s4212 (pattern : Twelve) : d1785 (change pattern 11 12) = d2871 pattern := by
  change (if pattern.h then d679 (change pattern 11 12) else d1782 (change pattern 11 12)) = d2871 pattern
  rw [s4125, s4211]
  rfl
theorem s4213 (pattern : Twelve) : d1793 (change pattern 11 12) = d2872 pattern := by
  change (if pattern.f then d1785 (change pattern 11 12) else d1569 (change pattern 11 12)) = d2872 pattern
  rw [s4212, s4161]
  rfl
theorem s4214 (pattern : Twelve) : d1655 (change pattern 11 12) = d2873 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d822 (change pattern 11 12)) = d2873 pattern
  rw [s4038, s4087]
  rfl
theorem s4215 (pattern : Twelve) : d1800 (change pattern 11 12) = d2874 pattern := by
  change (if pattern.e then d1655 (change pattern 11 12) else d1793 (change pattern 11 12)) = d2874 pattern
  rw [s4214, s4213]
  rfl
theorem s4216 (pattern : Twelve) : d1805 (change pattern 11 12) = d2875 pattern := by
  change (if pattern.j then d1800 (change pattern 11 12) else d1799 (change pattern 11 12)) = d2875 pattern
  rw [s4215, s4210]
  rfl
theorem s4217 (pattern : Twelve) : d1806 (change pattern 11 12) = d2876 pattern := by
  change (if pattern.j then d6 (change pattern 11 12) else d1798 (change pattern 11 12)) = d2876 pattern
  rw [s4038, s4206]
  rfl
theorem s4218 (pattern : Twelve) : d1809 (change pattern 11 12) = d2877 pattern := by
  change (if pattern.d then d1806 (change pattern 11 12) else d1805 (change pattern 11 12)) = d2877 pattern
  rw [s4217, s4216]
  rfl
theorem s4219 (pattern : Twelve) : d1811 (change pattern 11 12) = d2878 pattern := by
  change (if pattern.c then d1809 (change pattern 11 12) else d1804 (change pattern 11 12)) = d2878 pattern
  rw [s4218, s4207]
  rfl
theorem s4220 (pattern : Twelve) : d1794 (change pattern 11 12) = d2879 pattern := by
  change (if pattern.f then d1780 (change pattern 11 12) else d636 (change pattern 11 12)) = d2879 pattern
  rw [s4202, s4027]
  rfl
theorem s4221 (pattern : Twelve) : d1801 (change pattern 11 12) = d2880 pattern := by
  change (if pattern.e then d1789 (change pattern 11 12) else d1794 (change pattern 11 12)) = d2880 pattern
  rw [s4200, s4220]
  rfl
theorem s4222 (pattern : Twelve) : d1807 (change pattern 11 12) = d2881 pattern := by
  change (if pattern.j then d1798 (change pattern 11 12) else d1801 (change pattern 11 12)) = d2881 pattern
  rw [s4206, s4221]
  rfl
theorem s4223 (pattern : Twelve) : d1783 (change pattern 11 12) = d2882 pattern := by
  change (if pattern.i then d22 (change pattern 11 12) else d635 (change pattern 11 12)) = d2882 pattern
  rw [s4122, s4171]
  rfl
theorem s4224 (pattern : Twelve) : d1786 (change pattern 11 12) = d2883 pattern := by
  change (if pattern.h then d1783 (change pattern 11 12) else d1780 (change pattern 11 12)) = d2883 pattern
  rw [s4223, s4202]
  rfl
theorem s4225 (pattern : Twelve) : d1795 (change pattern 11 12) = d2884 pattern := by
  change (if pattern.f then d1786 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2884 pattern
  rw [s4224, s4037]
  rfl
theorem s4226 (pattern : Twelve) : d1802 (change pattern 11 12) = d2885 pattern := by
  change (if pattern.e then d1584 (change pattern 11 12) else d1795 (change pattern 11 12)) = d2885 pattern
  rw [s4162, s4225]
  rfl
theorem s4227 (pattern : Twelve) : d183 (change pattern 11 12) = d2886 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d22 (change pattern 11 12)) = d2886 pattern
  rw [s4038, s4122]
  rfl
theorem s4228 (pattern : Twelve) : d1787 (change pattern 11 12) = d2887 pattern := by
  change (if pattern.h then d183 (change pattern 11 12) else d679 (change pattern 11 12)) = d2887 pattern
  rw [s4227, s4125]
  rfl
theorem s4229 (pattern : Twelve) : d1796 (change pattern 11 12) = d2888 pattern := by
  change (if pattern.f then d1787 (change pattern 11 12) else d1569 (change pattern 11 12)) = d2888 pattern
  rw [s4228, s4161]
  rfl
theorem s4230 (pattern : Twelve) : d1252 (change pattern 11 12) = d2889 pattern := by
  change (if pattern.h then d6 (change pattern 11 12) else d822 (change pattern 11 12)) = d2889 pattern
  rw [s4038, s4087]
  rfl
theorem s4231 (pattern : Twelve) : d1626 (change pattern 11 12) = d2890 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1252 (change pattern 11 12)) = d2890 pattern
  rw [s4038, s4230]
  rfl
theorem s4232 (pattern : Twelve) : d1803 (change pattern 11 12) = d2891 pattern := by
  change (if pattern.e then d1626 (change pattern 11 12) else d1796 (change pattern 11 12)) = d2891 pattern
  rw [s4231, s4229]
  rfl
theorem s4233 (pattern : Twelve) : d1808 (change pattern 11 12) = d2892 pattern := by
  change (if pattern.j then d1803 (change pattern 11 12) else d1802 (change pattern 11 12)) = d2892 pattern
  rw [s4232, s4226]
  rfl
theorem s4234 (pattern : Twelve) : d1810 (change pattern 11 12) = d2893 pattern := by
  change (if pattern.d then d1806 (change pattern 11 12) else d1808 (change pattern 11 12)) = d2893 pattern
  rw [s4217, s4233]
  rfl
theorem s4235 (pattern : Twelve) : d1812 (change pattern 11 12) = d2894 pattern := by
  change (if pattern.c then d1810 (change pattern 11 12) else d1807 (change pattern 11 12)) = d2894 pattern
  rw [s4234, s4222]
  rfl
theorem s4236 (pattern : Twelve) : d1813 (change pattern 11 12) = d2895 pattern := by
  change (if pattern.a then d1812 (change pattern 11 12) else d1811 (change pattern 11 12)) = d2895 pattern
  rw [s4235, s4219]
  rfl
theorem s4237 (pattern : Twelve) : d0 (change pattern 11 10) = d0 pattern := by
  rfl
theorem s4238 (pattern : Twelve) : d7 (change pattern 11 10) = d0 pattern := by
  change d0 (change pattern 11 10) = d0 pattern
  exact s4237 pattern
theorem s4239 (pattern : Twelve) : d646 (change pattern 11 10) = d0 pattern := by
  change (if pattern.i then d7 (change pattern 11 10) else d0 (change pattern 11 10)) = d0 pattern
  rw [s4238, s4237]
  simp only [ite_self]
theorem s4240 (pattern : Twelve) : d158 (change pattern 11 10) = d0 pattern := by
  change d0 (change pattern 11 10) = d0 pattern
  exact s4237 pattern
theorem s4241 (pattern : Twelve) : d634 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4242 (pattern : Twelve) : d647 (change pattern 11 10) = d0 pattern := by
  change (if pattern.i then d634 (change pattern 11 10) else d0 (change pattern 11 10)) = d0 pattern
  rw [s4241, s4237]
  simp only [ite_self]
theorem s4243 (pattern : Twelve) : d680 (change pattern 11 10) = d0 pattern := by
  change (if pattern.h then d647 (change pattern 11 10) else d646 (change pattern 11 10)) = d0 pattern
  rw [s4242, s4239]
  simp only [ite_self]
theorem s4244 (pattern : Twelve) : d1 (change pattern 11 10) = d1 pattern := by
  rfl
theorem s4245 (pattern : Twelve) : d157 (change pattern 11 10) = d1 pattern := by
  change d1 (change pattern 11 10) = d1 pattern
  exact s4244 pattern
theorem s4246 (pattern : Twelve) : d161 (change pattern 11 10) = d1 pattern := by
  change d157 (change pattern 11 10) = d1 pattern
  exact s4245 pattern
theorem s4247 (pattern : Twelve) : d171 (change pattern 11 10) = d26 pattern := by
  change (if pattern.i then d161 (change pattern 11 10) else d0 (change pattern 11 10)) = d26 pattern
  rw [s4246, s4237]
  rfl
theorem s4248 (pattern : Twelve) : d162 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4249 (pattern : Twelve) : d648 (change pattern 11 10) = d26 pattern := by
  change (if pattern.i then d157 (change pattern 11 10) else d162 (change pattern 11 10)) = d26 pattern
  rw [s4245, s4248]
  rfl
theorem s4250 (pattern : Twelve) : d681 (change pattern 11 10) = d26 pattern := by
  change (if pattern.h then d648 (change pattern 11 10) else d171 (change pattern 11 10)) = d26 pattern
  rw [s4249, s4247]
  simp only [ite_self]
theorem s4251 (pattern : Twelve) : d709 (change pattern 11 10) = d2593 pattern := by
  change (if pattern.f then d681 (change pattern 11 10) else d680 (change pattern 11 10)) = d2593 pattern
  rw [s4250, s4243]
  rfl
theorem s4252 (pattern : Twelve) : d649 (change pattern 11 10) = d0 pattern := by
  change (if pattern.i then d158 (change pattern 11 10) else d162 (change pattern 11 10)) = d0 pattern
  rw [s4240, s4248]
  simp only [ite_self]
theorem s4253 (pattern : Twelve) : d682 (change pattern 11 10) = d0 pattern := by
  change (if pattern.h then d649 (change pattern 11 10) else d647 (change pattern 11 10)) = d0 pattern
  rw [s4252, s4242]
  simp only [ite_self]
theorem s4254 (pattern : Twelve) : d2 (change pattern 11 10) = d2 pattern := by
  rfl
theorem s4255 (pattern : Twelve) : d160 (change pattern 11 10) = d2 pattern := by
  change d2 (change pattern 11 10) = d2 pattern
  exact s4254 pattern
theorem s4256 (pattern : Twelve) : d635 (change pattern 11 10) = d2 pattern := by
  change d160 (change pattern 11 10) = d2 pattern
  exact s4255 pattern
theorem s4257 (pattern : Twelve) : d650 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d635 (change pattern 11 10) else d162 (change pattern 11 10)) = d30 pattern
  rw [s4256, s4248]
  rfl
theorem s4258 (pattern : Twelve) : d636 (change pattern 11 10) = d1 pattern := by
  change d157 (change pattern 11 10) = d1 pattern
  exact s4245 pattern
theorem s4259 (pattern : Twelve) : d6 (change pattern 11 10) = d6 pattern := by
  rfl
theorem s4260 (pattern : Twelve) : d651 (change pattern 11 10) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d636 (change pattern 11 10)) = d45 pattern
  rw [s4259, s4258]
  rfl
theorem s4261 (pattern : Twelve) : d683 (change pattern 11 10) = d65 pattern := by
  change (if pattern.h then d651 (change pattern 11 10) else d650 (change pattern 11 10)) = d65 pattern
  rw [s4260, s4257]
  rfl
theorem s4262 (pattern : Twelve) : d710 (change pattern 11 10) = d2896 pattern := by
  change (if pattern.f then d683 (change pattern 11 10) else d682 (change pattern 11 10)) = d2896 pattern
  rw [s4261, s4253]
  rfl
theorem s4263 (pattern : Twelve) : d736 (change pattern 11 10) = d2897 pattern := by
  change (if pattern.e then d710 (change pattern 11 10) else d709 (change pattern 11 10)) = d2897 pattern
  rw [s4262, s4251]
  rfl
theorem s4264 (pattern : Twelve) : d10 (change pattern 11 10) = d0 pattern := by
  change d0 (change pattern 11 10) = d0 pattern
  exact s4237 pattern
theorem s4265 (pattern : Twelve) : d637 (change pattern 11 10) = d2 pattern := by
  change d160 (change pattern 11 10) = d2 pattern
  exact s4255 pattern
theorem s4266 (pattern : Twelve) : d652 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d637 (change pattern 11 10) else d10 (change pattern 11 10)) = d30 pattern
  rw [s4265, s4264]
  rfl
theorem s4267 (pattern : Twelve) : d638 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4268 (pattern : Twelve) : d4 (change pattern 11 10) = d4 pattern := by
  rfl
theorem s4269 (pattern : Twelve) : d13 (change pattern 11 10) = d4 pattern := by
  change d4 (change pattern 11 10) = d4 pattern
  exact s4268 pattern
theorem s4270 (pattern : Twelve) : d639 (change pattern 11 10) = d4 pattern := by
  change d13 (change pattern 11 10) = d4 pattern
  exact s4269 pattern
theorem s4271 (pattern : Twelve) : d653 (change pattern 11 10) = d2635 pattern := by
  change (if pattern.i then d639 (change pattern 11 10) else d638 (change pattern 11 10)) = d2635 pattern
  rw [s4270, s4267]
  rfl
theorem s4272 (pattern : Twelve) : d684 (change pattern 11 10) = d2636 pattern := by
  change (if pattern.h then d653 (change pattern 11 10) else d652 (change pattern 11 10)) = d2636 pattern
  rw [s4271, s4266]
  rfl
theorem s4273 (pattern : Twelve) : d654 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 10) else d638 (change pattern 11 10)) = d30 pattern
  rw [s4255, s4267]
  rfl
theorem s4274 (pattern : Twelve) : d5 (change pattern 11 10) = d5 pattern := by
  rfl
theorem s4275 (pattern : Twelve) : d14 (change pattern 11 10) = d5 pattern := by
  change d5 (change pattern 11 10) = d5 pattern
  exact s4274 pattern
theorem s4276 (pattern : Twelve) : d21 (change pattern 11 10) = d5 pattern := by
  change d14 (change pattern 11 10) = d5 pattern
  exact s4275 pattern
theorem s4277 (pattern : Twelve) : d655 (change pattern 11 10) = d2898 pattern := by
  change (if pattern.i then d21 (change pattern 11 10) else d158 (change pattern 11 10)) = d2898 pattern
  rw [s4276, s4240]
  rfl
theorem s4278 (pattern : Twelve) : d685 (change pattern 11 10) = d2899 pattern := by
  change (if pattern.h then d655 (change pattern 11 10) else d654 (change pattern 11 10)) = d2899 pattern
  rw [s4277, s4273]
  rfl
theorem s4279 (pattern : Twelve) : d711 (change pattern 11 10) = d2900 pattern := by
  change (if pattern.f then d685 (change pattern 11 10) else d684 (change pattern 11 10)) = d2900 pattern
  rw [s4278, s4272]
  rfl
theorem s4280 (pattern : Twelve) : d22 (change pattern 11 10) = d6 pattern := by
  change d6 (change pattern 11 10) = d6 pattern
  exact s4259 pattern
theorem s4281 (pattern : Twelve) : d656 (change pattern 11 10) = d35 pattern := by
  change (if pattern.i then d22 (change pattern 11 10) else d158 (change pattern 11 10)) = d35 pattern
  rw [s4280, s4240]
  rfl
theorem s4282 (pattern : Twelve) : d686 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d656 (change pattern 11 10) else d654 (change pattern 11 10)) = d56 pattern
  rw [s4281, s4273]
  rfl
theorem s4283 (pattern : Twelve) : d657 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 10) else d158 (change pattern 11 10)) = d30 pattern
  rw [s4255, s4240]
  rfl
theorem s4284 (pattern : Twelve) : d687 (change pattern 11 10) = d65 pattern := by
  change (if pattern.h then d651 (change pattern 11 10) else d657 (change pattern 11 10)) = d65 pattern
  rw [s4260, s4283]
  rfl
theorem s4285 (pattern : Twelve) : d712 (change pattern 11 10) = d85 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d686 (change pattern 11 10)) = d85 pattern
  rw [s4284, s4282]
  rfl
theorem s4286 (pattern : Twelve) : d737 (change pattern 11 10) = d2901 pattern := by
  change (if pattern.e then d712 (change pattern 11 10) else d711 (change pattern 11 10)) = d2901 pattern
  rw [s4285, s4279]
  rfl
theorem s4287 (pattern : Twelve) : d754 (change pattern 11 10) = d2902 pattern := by
  change (if pattern.j then d737 (change pattern 11 10) else d736 (change pattern 11 10)) = d2902 pattern
  rw [s4286, s4263]
  rfl
theorem s4288 (pattern : Twelve) : d640 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4289 (pattern : Twelve) : d658 (change pattern 11 10) = d0 pattern := by
  change (if pattern.i then d640 (change pattern 11 10) else d10 (change pattern 11 10)) = d0 pattern
  rw [s4288, s4264]
  simp only [ite_self]
theorem s4290 (pattern : Twelve) : d659 (change pattern 11 10) = d0 pattern := by
  change (if pattern.i then d158 (change pattern 11 10) else d638 (change pattern 11 10)) = d0 pattern
  rw [s4240, s4267]
  simp only [ite_self]
theorem s4291 (pattern : Twelve) : d688 (change pattern 11 10) = d0 pattern := by
  change (if pattern.h then d659 (change pattern 11 10) else d658 (change pattern 11 10)) = d0 pattern
  rw [s4290, s4289]
  simp only [ite_self]
theorem s4292 (pattern : Twelve) : d660 (change pattern 11 10) = d26 pattern := by
  change (if pattern.i then d157 (change pattern 11 10) else d638 (change pattern 11 10)) = d26 pattern
  rw [s4245, s4267]
  rfl
theorem s4293 (pattern : Twelve) : d661 (change pattern 11 10) = d26 pattern := by
  change (if pattern.i then d157 (change pattern 11 10) else d158 (change pattern 11 10)) = d26 pattern
  rw [s4245, s4240]
  rfl
theorem s4294 (pattern : Twelve) : d689 (change pattern 11 10) = d26 pattern := by
  change (if pattern.h then d661 (change pattern 11 10) else d660 (change pattern 11 10)) = d26 pattern
  rw [s4293, s4292]
  simp only [ite_self]
theorem s4295 (pattern : Twelve) : d713 (change pattern 11 10) = d2593 pattern := by
  change (if pattern.f then d689 (change pattern 11 10) else d688 (change pattern 11 10)) = d2593 pattern
  rw [s4294, s4291]
  rfl
theorem s4296 (pattern : Twelve) : d690 (change pattern 11 10) = d0 pattern := by
  change (if pattern.h then d158 (change pattern 11 10) else d659 (change pattern 11 10)) = d0 pattern
  rw [s4240, s4290]
  simp only [ite_self]
theorem s4297 (pattern : Twelve) : d714 (change pattern 11 10) = d2896 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d690 (change pattern 11 10)) = d2896 pattern
  rw [s4284, s4296]
  rfl
theorem s4298 (pattern : Twelve) : d738 (change pattern 11 10) = d2897 pattern := by
  change (if pattern.e then d714 (change pattern 11 10) else d713 (change pattern 11 10)) = d2897 pattern
  rw [s4297, s4295]
  rfl
theorem s4299 (pattern : Twelve) : d641 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4300 (pattern : Twelve) : d662 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 10) else d641 (change pattern 11 10)) = d30 pattern
  rw [s4255, s4299]
  rfl
theorem s4301 (pattern : Twelve) : d663 (change pattern 11 10) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d158 (change pattern 11 10)) = d35 pattern
  rw [s4259, s4240]
  rfl
theorem s4302 (pattern : Twelve) : d691 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 10) else d662 (change pattern 11 10)) = d56 pattern
  rw [s4301, s4300]
  rfl
theorem s4303 (pattern : Twelve) : d692 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 10) else d657 (change pattern 11 10)) = d56 pattern
  rw [s4301, s4283]
  rfl
theorem s4304 (pattern : Twelve) : d715 (change pattern 11 10) = d56 pattern := by
  change (if pattern.f then d692 (change pattern 11 10) else d691 (change pattern 11 10)) = d56 pattern
  rw [s4303, s4302]
  simp only [ite_self]
theorem s4305 (pattern : Twelve) : d716 (change pattern 11 10) = d85 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d692 (change pattern 11 10)) = d85 pattern
  rw [s4284, s4303]
  rfl
theorem s4306 (pattern : Twelve) : d739 (change pattern 11 10) = d2903 pattern := by
  change (if pattern.e then d716 (change pattern 11 10) else d715 (change pattern 11 10)) = d2903 pattern
  rw [s4305, s4304]
  rfl
theorem s4307 (pattern : Twelve) : d755 (change pattern 11 10) = d2904 pattern := by
  change (if pattern.j then d739 (change pattern 11 10) else d738 (change pattern 11 10)) = d2904 pattern
  rw [s4306, s4298]
  rfl
theorem s4308 (pattern : Twelve) : d766 (change pattern 11 10) = d2905 pattern := by
  change (if pattern.d then d755 (change pattern 11 10) else d754 (change pattern 11 10)) = d2905 pattern
  rw [s4307, s4287]
  rfl
theorem s4309 (pattern : Twelve) : d630 (change pattern 11 10) = d0 pattern := by
  change d0 (change pattern 11 10) = d0 pattern
  exact s4237 pattern
theorem s4310 (pattern : Twelve) : d642 (change pattern 11 10) = d2 pattern := by
  change d160 (change pattern 11 10) = d2 pattern
  exact s4255 pattern
theorem s4311 (pattern : Twelve) : d664 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d642 (change pattern 11 10) else d630 (change pattern 11 10)) = d30 pattern
  rw [s4310, s4309]
  rfl
theorem s4312 (pattern : Twelve) : d665 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 10) else d640 (change pattern 11 10)) = d30 pattern
  rw [s4255, s4288]
  rfl
theorem s4313 (pattern : Twelve) : d693 (change pattern 11 10) = d30 pattern := by
  change (if pattern.h then d665 (change pattern 11 10) else d664 (change pattern 11 10)) = d30 pattern
  rw [s4312, s4311]
  simp only [ite_self]
theorem s4314 (pattern : Twelve) : d3 (change pattern 11 10) = d3 pattern := by
  rfl
theorem s4315 (pattern : Twelve) : d159 (change pattern 11 10) = d3 pattern := by
  change d3 (change pattern 11 10) = d3 pattern
  exact s4314 pattern
theorem s4316 (pattern : Twelve) : d666 (change pattern 11 10) = d123 pattern := by
  change (if pattern.i then d159 (change pattern 11 10) else d158 (change pattern 11 10)) = d123 pattern
  rw [s4315, s4240]
  rfl
theorem s4317 (pattern : Twelve) : d694 (change pattern 11 10) = d132 pattern := by
  change (if pattern.h then d666 (change pattern 11 10) else d665 (change pattern 11 10)) = d132 pattern
  rw [s4316, s4312]
  rfl
theorem s4318 (pattern : Twelve) : d717 (change pattern 11 10) = d2614 pattern := by
  change (if pattern.f then d694 (change pattern 11 10) else d693 (change pattern 11 10)) = d2614 pattern
  rw [s4317, s4313]
  rfl
theorem s4319 (pattern : Twelve) : d695 (change pattern 11 10) = d30 pattern := by
  change (if pattern.h then d657 (change pattern 11 10) else d665 (change pattern 11 10)) = d30 pattern
  rw [s4283, s4312]
  simp only [ite_self]
theorem s4320 (pattern : Twelve) : d718 (change pattern 11 10) = d2906 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d695 (change pattern 11 10)) = d2906 pattern
  rw [s4284, s4319]
  rfl
theorem s4321 (pattern : Twelve) : d740 (change pattern 11 10) = d2907 pattern := by
  change (if pattern.e then d718 (change pattern 11 10) else d717 (change pattern 11 10)) = d2907 pattern
  rw [s4320, s4318]
  rfl
theorem s4322 (pattern : Twelve) : d643 (change pattern 11 10) = d2 pattern := by
  change d160 (change pattern 11 10) = d2 pattern
  exact s4255 pattern
theorem s4323 (pattern : Twelve) : d667 (change pattern 11 10) = d38 pattern := by
  change (if pattern.i then d13 (change pattern 11 10) else d643 (change pattern 11 10)) = d38 pattern
  rw [s4269, s4322]
  rfl
theorem s4324 (pattern : Twelve) : d668 (change pattern 11 10) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d160 (change pattern 11 10)) = d39 pattern
  rw [s4259, s4255]
  rfl
theorem s4325 (pattern : Twelve) : d696 (change pattern 11 10) = d59 pattern := by
  change (if pattern.h then d668 (change pattern 11 10) else d667 (change pattern 11 10)) = d59 pattern
  rw [s4324, s4323]
  rfl
theorem s4326 (pattern : Twelve) : d669 (change pattern 11 10) = d38 pattern := by
  change (if pattern.i then d13 (change pattern 11 10) else d160 (change pattern 11 10)) = d38 pattern
  rw [s4269, s4255]
  rfl
theorem s4327 (pattern : Twelve) : d697 (change pattern 11 10) = d59 pattern := by
  change (if pattern.h then d668 (change pattern 11 10) else d669 (change pattern 11 10)) = d59 pattern
  rw [s4324, s4326]
  rfl
theorem s4328 (pattern : Twelve) : d719 (change pattern 11 10) = d59 pattern := by
  change (if pattern.f then d697 (change pattern 11 10) else d696 (change pattern 11 10)) = d59 pattern
  rw [s4327, s4325]
  simp only [ite_self]
theorem s4329 (pattern : Twelve) : d644 (change pattern 11 10) = d3 pattern := by
  change d159 (change pattern 11 10) = d3 pattern
  exact s4315 pattern
theorem s4330 (pattern : Twelve) : d670 (change pattern 11 10) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d644 (change pattern 11 10)) = d47 pattern
  rw [s4259, s4329]
  rfl
theorem s4331 (pattern : Twelve) : d698 (change pattern 11 10) = d69 pattern := by
  change (if pattern.h then d670 (change pattern 11 10) else d669 (change pattern 11 10)) = d69 pattern
  rw [s4330, s4326]
  rfl
theorem s4332 (pattern : Twelve) : d720 (change pattern 11 10) = d89 pattern := by
  change (if pattern.f then d698 (change pattern 11 10) else d697 (change pattern 11 10)) = d89 pattern
  rw [s4331, s4327]
  rfl
theorem s4333 (pattern : Twelve) : d741 (change pattern 11 10) = d2908 pattern := by
  change (if pattern.e then d720 (change pattern 11 10) else d719 (change pattern 11 10)) = d2908 pattern
  rw [s4332, s4328]
  rfl
theorem s4334 (pattern : Twelve) : d756 (change pattern 11 10) = d2909 pattern := by
  change (if pattern.j then d741 (change pattern 11 10) else d740 (change pattern 11 10)) = d2909 pattern
  rw [s4333, s4321]
  rfl
theorem s4335 (pattern : Twelve) : d645 (change pattern 11 10) = d0 pattern := by
  change d158 (change pattern 11 10) = d0 pattern
  exact s4240 pattern
theorem s4336 (pattern : Twelve) : d671 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 10) else d645 (change pattern 11 10)) = d30 pattern
  rw [s4255, s4335]
  rfl
theorem s4337 (pattern : Twelve) : d699 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 10) else d671 (change pattern 11 10)) = d56 pattern
  rw [s4301, s4336]
  rfl
theorem s4338 (pattern : Twelve) : d721 (change pattern 11 10) = d56 pattern := by
  change (if pattern.f then d692 (change pattern 11 10) else d699 (change pattern 11 10)) = d56 pattern
  rw [s4303, s4337]
  simp only [ite_self]
theorem s4339 (pattern : Twelve) : d742 (change pattern 11 10) = d2903 pattern := by
  change (if pattern.e then d716 (change pattern 11 10) else d721 (change pattern 11 10)) = d2903 pattern
  rw [s4305, s4338]
  rfl
theorem s4340 (pattern : Twelve) : d757 (change pattern 11 10) = d2910 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d742 (change pattern 11 10)) = d2910 pattern
  rw [s4259, s4339]
  rfl
theorem s4341 (pattern : Twelve) : d767 (change pattern 11 10) = d2911 pattern := by
  change (if pattern.d then d757 (change pattern 11 10) else d756 (change pattern 11 10)) = d2911 pattern
  rw [s4340, s4334]
  rfl
theorem s4342 (pattern : Twelve) : d772 (change pattern 11 10) = d2912 pattern := by
  change (if pattern.c then d767 (change pattern 11 10) else d766 (change pattern 11 10)) = d2912 pattern
  rw [s4341, s4308]
  rfl
theorem s4343 (pattern : Twelve) : d722 (change pattern 11 10) = d2593 pattern := by
  change (if pattern.f then d661 (change pattern 11 10) else d158 (change pattern 11 10)) = d2593 pattern
  rw [s4293, s4240]
  rfl
theorem s4344 (pattern : Twelve) : d672 (change pattern 11 10) = d30 pattern := by
  change (if pattern.i then d635 (change pattern 11 10) else d158 (change pattern 11 10)) = d30 pattern
  rw [s4256, s4240]
  rfl
theorem s4345 (pattern : Twelve) : d700 (change pattern 11 10) = d65 pattern := by
  change (if pattern.h then d651 (change pattern 11 10) else d672 (change pattern 11 10)) = d65 pattern
  rw [s4260, s4344]
  rfl
theorem s4346 (pattern : Twelve) : d723 (change pattern 11 10) = d2896 pattern := by
  change (if pattern.f then d700 (change pattern 11 10) else d158 (change pattern 11 10)) = d2896 pattern
  rw [s4345, s4240]
  rfl
theorem s4347 (pattern : Twelve) : d743 (change pattern 11 10) = d2897 pattern := by
  change (if pattern.e then d723 (change pattern 11 10) else d722 (change pattern 11 10)) = d2897 pattern
  rw [s4346, s4343]
  rfl
theorem s4348 (pattern : Twelve) : d673 (change pattern 11 10) = d2635 pattern := by
  change (if pattern.i then d639 (change pattern 11 10) else d158 (change pattern 11 10)) = d2635 pattern
  rw [s4270, s4240]
  rfl
theorem s4349 (pattern : Twelve) : d701 (change pattern 11 10) = d2636 pattern := by
  change (if pattern.h then d673 (change pattern 11 10) else d657 (change pattern 11 10)) = d2636 pattern
  rw [s4348, s4283]
  rfl
end NetHack.Sokoban21.Diagram
