/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions04
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s750 (pattern : Ten) : d0 (change pattern 9 10) = d0 pattern := by
  rfl
theorem s751 (pattern : Ten) : d86 (change pattern 9 10) = d0 pattern := by
  change d0 (change pattern 9 10) = d0 pattern
  exact s750 pattern
theorem s752 (pattern : Ten) : d87 (change pattern 9 10) = d0 pattern := by
  change (if pattern.i then d0 (change pattern 9 10) else d86 (change pattern 9 10)) = d0 pattern
  rw [s750, s751]
  simp only [ite_self]
theorem s753 (pattern : Ten) : d10 (change pattern 9 10) = d10 pattern := by
  rfl
theorem s754 (pattern : Ten) : d88 (change pattern 9 10) = d88 pattern := by
  change (if pattern.i then d10 (change pattern 9 10) else d0 (change pattern 9 10)) = d88 pattern
  rw [s753, s750]
  rfl
theorem s755 (pattern : Ten) : d93 (change pattern 9 10) = d468 pattern := by
  change (if pattern.h then d88 (change pattern 9 10) else d87 (change pattern 9 10)) = d468 pattern
  rw [s754, s752]
  rfl
theorem s756 (pattern : Ten) : d9 (change pattern 9 10) = d9 pattern := by
  rfl
theorem s757 (pattern : Ten) : d11 (change pattern 9 10) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 9 10) else d9 (change pattern 9 10)) = d11 pattern
  rw [s753, s756]
  rfl
theorem s758 (pattern : Ten) : d89 (change pattern 9 10) = d89 pattern := by
  change (if pattern.i then d11 (change pattern 9 10) else d0 (change pattern 9 10)) = d89 pattern
  rw [s757, s750]
  rfl
theorem s759 (pattern : Ten) : d90 (change pattern 9 10) = d90 pattern := by
  change (if pattern.i then d10 (change pattern 9 10) else d11 (change pattern 9 10)) = d90 pattern
  rw [s753, s757]
  rfl
theorem s760 (pattern : Ten) : d94 (change pattern 9 10) = d94 pattern := by
  change (if pattern.h then d90 (change pattern 9 10) else d89 (change pattern 9 10)) = d94 pattern
  rw [s759, s758]
  rfl
theorem s761 (pattern : Ten) : d99 (change pattern 9 10) = d469 pattern := by
  change (if pattern.g then d94 (change pattern 9 10) else d93 (change pattern 9 10)) = d469 pattern
  rw [s760, s755]
  rfl
theorem s762 (pattern : Ten) : d2 (change pattern 9 10) = d2 pattern := by
  rfl
theorem s763 (pattern : Ten) : d91 (change pattern 9 10) = d91 pattern := by
  change (if pattern.i then d2 (change pattern 9 10) else d0 (change pattern 9 10)) = d91 pattern
  rw [s762, s750]
  rfl
theorem s764 (pattern : Ten) : d92 (change pattern 9 10) = d92 pattern := by
  change (if pattern.i then d10 (change pattern 9 10) else d2 (change pattern 9 10)) = d92 pattern
  rw [s753, s762]
  rfl
theorem s765 (pattern : Ten) : d95 (change pattern 9 10) = d95 pattern := by
  change (if pattern.h then d92 (change pattern 9 10) else d91 (change pattern 9 10)) = d95 pattern
  rw [s764, s763]
  rfl
theorem s766 (pattern : Ten) : d100 (change pattern 9 10) = d100 pattern := by
  change (if pattern.g then d94 (change pattern 9 10) else d95 (change pattern 9 10)) = d100 pattern
  rw [s760, s765]
  rfl
theorem s767 (pattern : Ten) : d103 (change pattern 9 10) = d470 pattern := by
  change (if pattern.c then d100 (change pattern 9 10) else d99 (change pattern 9 10)) = d470 pattern
  rw [s766, s761]
  rfl
theorem s768 (pattern : Ten) : d96 (change pattern 9 10) = d96 pattern := by
  change (if pattern.h then d10 (change pattern 9 10) else d88 (change pattern 9 10)) = d96 pattern
  rw [s753, s754]
  rfl
theorem s769 (pattern : Ten) : d97 (change pattern 9 10) = d97 pattern := by
  change (if pattern.h then d10 (change pattern 9 10) else d90 (change pattern 9 10)) = d97 pattern
  rw [s753, s759]
  rfl
theorem s770 (pattern : Ten) : d101 (change pattern 9 10) = d101 pattern := by
  change (if pattern.g then d97 (change pattern 9 10) else d96 (change pattern 9 10)) = d101 pattern
  rw [s769, s768]
  rfl
theorem s771 (pattern : Ten) : d98 (change pattern 9 10) = d98 pattern := by
  change (if pattern.h then d10 (change pattern 9 10) else d92 (change pattern 9 10)) = d98 pattern
  rw [s753, s764]
  rfl
theorem s772 (pattern : Ten) : d102 (change pattern 9 10) = d102 pattern := by
  change (if pattern.g then d97 (change pattern 9 10) else d98 (change pattern 9 10)) = d102 pattern
  rw [s769, s771]
  rfl
theorem s773 (pattern : Ten) : d104 (change pattern 9 10) = d104 pattern := by
  change (if pattern.c then d102 (change pattern 9 10) else d101 (change pattern 9 10)) = d104 pattern
  rw [s772, s770]
  rfl
theorem s774 (pattern : Ten) : d105 (change pattern 9 10) = d471 pattern := by
  change (if pattern.e then d104 (change pattern 9 10) else d103 (change pattern 9 10)) = d471 pattern
  rw [s773, s767]
  rfl
theorem s775 (pattern : Ten) : d106 (change pattern 9 10) = d106 pattern := by
  change (if pattern.e then d10 (change pattern 9 10) else d104 (change pattern 9 10)) = d106 pattern
  rw [s753, s773]
  rfl
theorem s776 (pattern : Ten) : d107 (change pattern 9 10) = d472 pattern := by
  change (if pattern.d then d106 (change pattern 9 10) else d105 (change pattern 9 10)) = d472 pattern
  rw [s775, s774]
  rfl
theorem s777 (pattern : Ten) : d1 (change pattern 9 10) = d1 pattern := by
  rfl
theorem s778 (pattern : Ten) : d171 (change pattern 9 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 9 10) else d0 (change pattern 9 10)) = d171 pattern
  rw [s777, s750]
  rfl
theorem s779 (pattern : Ten) : d173 (change pattern 9 10) = d171 pattern := by
  change d171 (change pattern 9 10) = d171 pattern
  exact s778 pattern
theorem s780 (pattern : Ten) : d249 (change pattern 9 10) = d171 pattern := by
  change (if pattern.i then d171 (change pattern 9 10) else d173 (change pattern 9 10)) = d171 pattern
  rw [s778, s779]
  simp only [ite_self]
theorem s781 (pattern : Ten) : d250 (change pattern 9 10) = d250 pattern := by
  change (if pattern.i then d10 (change pattern 9 10) else d171 (change pattern 9 10)) = d250 pattern
  rw [s753, s778]
  rfl
theorem s782 (pattern : Ten) : d253 (change pattern 9 10) = d473 pattern := by
  change (if pattern.h then d250 (change pattern 9 10) else d249 (change pattern 9 10)) = d473 pattern
  rw [s781, s780]
  rfl
theorem s783 (pattern : Ten) : d254 (change pattern 9 10) = d254 pattern := by
  change (if pattern.h then d10 (change pattern 9 10) else d250 (change pattern 9 10)) = d254 pattern
  rw [s753, s781]
  rfl
theorem s784 (pattern : Ten) : d257 (change pattern 9 10) = d474 pattern := by
  change (if pattern.g then d254 (change pattern 9 10) else d253 (change pattern 9 10)) = d474 pattern
  rw [s783, s782]
  rfl
theorem s785 (pattern : Ten) : d3 (change pattern 9 10) = d3 pattern := by
  rfl
theorem s786 (pattern : Ten) : d172 (change pattern 9 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 9 10) else d2 (change pattern 9 10)) = d172 pattern
  rw [s785, s762]
  rfl
theorem s787 (pattern : Ten) : d251 (change pattern 9 10) = d251 pattern := by
  change (if pattern.i then d172 (change pattern 9 10) else d171 (change pattern 9 10)) = d251 pattern
  rw [s786, s778]
  rfl
theorem s788 (pattern : Ten) : d252 (change pattern 9 10) = d252 pattern := by
  change (if pattern.i then d10 (change pattern 9 10) else d172 (change pattern 9 10)) = d252 pattern
  rw [s753, s786]
  rfl
theorem s789 (pattern : Ten) : d255 (change pattern 9 10) = d255 pattern := by
  change (if pattern.h then d252 (change pattern 9 10) else d251 (change pattern 9 10)) = d255 pattern
  rw [s788, s787]
  rfl
theorem s790 (pattern : Ten) : d258 (change pattern 9 10) = d258 pattern := by
  change (if pattern.g then d254 (change pattern 9 10) else d255 (change pattern 9 10)) = d258 pattern
  rw [s783, s789]
  rfl
theorem s791 (pattern : Ten) : d261 (change pattern 9 10) = d475 pattern := by
  change (if pattern.c then d258 (change pattern 9 10) else d257 (change pattern 9 10)) = d475 pattern
  rw [s790, s784]
  rfl
theorem s792 (pattern : Ten) : d259 (change pattern 9 10) = d259 pattern := by
  change (if pattern.g then d10 (change pattern 9 10) else d254 (change pattern 9 10)) = d259 pattern
  rw [s753, s783]
  rfl
theorem s793 (pattern : Ten) : d256 (change pattern 9 10) = d256 pattern := by
  change (if pattern.h then d10 (change pattern 9 10) else d252 (change pattern 9 10)) = d256 pattern
  rw [s753, s788]
  rfl
theorem s794 (pattern : Ten) : d260 (change pattern 9 10) = d260 pattern := by
  change (if pattern.g then d10 (change pattern 9 10) else d256 (change pattern 9 10)) = d260 pattern
  rw [s753, s793]
  rfl
theorem s795 (pattern : Ten) : d262 (change pattern 9 10) = d262 pattern := by
  change (if pattern.c then d260 (change pattern 9 10) else d259 (change pattern 9 10)) = d262 pattern
  rw [s794, s792]
  rfl
theorem s796 (pattern : Ten) : d263 (change pattern 9 10) = d476 pattern := by
  change (if pattern.e then d262 (change pattern 9 10) else d261 (change pattern 9 10)) = d476 pattern
  rw [s795, s791]
  rfl
theorem s797 (pattern : Ten) : d264 (change pattern 9 10) = d264 pattern := by
  change (if pattern.e then d10 (change pattern 9 10) else d262 (change pattern 9 10)) = d264 pattern
  rw [s753, s795]
  rfl
theorem s798 (pattern : Ten) : d265 (change pattern 9 10) = d477 pattern := by
  change (if pattern.d then d264 (change pattern 9 10) else d263 (change pattern 9 10)) = d477 pattern
  rw [s797, s796]
  rfl
theorem s799 (pattern : Ten) : d0 (change pattern 8 7) = d0 pattern := by
  rfl
theorem s800 (pattern : Ten) : d2 (change pattern 8 7) = d2 pattern := by
  rfl
theorem s801 (pattern : Ten) : d15 (change pattern 8 7) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 8 7) else d0 (change pattern 8 7)) = d15 pattern
  rw [s800, s799]
  rfl
theorem s802 (pattern : Ten) : d109 (change pattern 8 7) = d15 pattern := by
  change d15 (change pattern 8 7) = d15 pattern
  exact s801 pattern
theorem s803 (pattern : Ten) : d9 (change pattern 8 7) = d9 pattern := by
  rfl
theorem s804 (pattern : Ten) : d10 (change pattern 8 7) = d10 pattern := by
  rfl
theorem s805 (pattern : Ten) : d11 (change pattern 8 7) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 8 7) else d9 (change pattern 8 7)) = d11 pattern
  rw [s804, s803]
  rfl
theorem s806 (pattern : Ten) : d14 (change pattern 8 7) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 8 7) else d11 (change pattern 8 7)) = d14 pattern
  rw [s804, s805]
  rfl
theorem s807 (pattern : Ten) : d110 (change pattern 8 7) = d14 pattern := by
  change d14 (change pattern 8 7) = d14 pattern
  exact s806 pattern
theorem s808 (pattern : Ten) : d115 (change pattern 8 7) = d481 pattern := by
  change (if pattern.g then d110 (change pattern 8 7) else d109 (change pattern 8 7)) = d481 pattern
  rw [s807, s802]
  rfl
theorem s809 (pattern : Ten) : d4 (change pattern 8 7) = d4 pattern := by
  rfl
theorem s810 (pattern : Ten) : d44 (change pattern 8 7) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 8 7) else d2 (change pattern 8 7)) = d44 pattern
  rw [s809, s800]
  rfl
theorem s811 (pattern : Ten) : d111 (change pattern 8 7) = d44 pattern := by
  change d44 (change pattern 8 7) = d44 pattern
  exact s810 pattern
theorem s812 (pattern : Ten) : d116 (change pattern 8 7) = d482 pattern := by
  change (if pattern.g then d110 (change pattern 8 7) else d111 (change pattern 8 7)) = d482 pattern
  rw [s807, s811]
  rfl
theorem s813 (pattern : Ten) : d119 (change pattern 8 7) = d483 pattern := by
  change (if pattern.c then d116 (change pattern 8 7) else d115 (change pattern 8 7)) = d483 pattern
  rw [s812, s808]
  rfl
theorem s814 (pattern : Ten) : d112 (change pattern 8 7) = d10 pattern := by
  change d10 (change pattern 8 7) = d10 pattern
  exact s804 pattern
theorem s815 (pattern : Ten) : d113 (change pattern 8 7) = d10 pattern := by
  change d10 (change pattern 8 7) = d10 pattern
  exact s804 pattern
theorem s816 (pattern : Ten) : d117 (change pattern 8 7) = d10 pattern := by
  change (if pattern.g then d113 (change pattern 8 7) else d112 (change pattern 8 7)) = d10 pattern
  rw [s815, s814]
  simp only [ite_self]
theorem s817 (pattern : Ten) : d114 (change pattern 8 7) = d10 pattern := by
  change d10 (change pattern 8 7) = d10 pattern
  exact s804 pattern
theorem s818 (pattern : Ten) : d118 (change pattern 8 7) = d10 pattern := by
  change (if pattern.g then d113 (change pattern 8 7) else d114 (change pattern 8 7)) = d10 pattern
  rw [s815, s817]
  simp only [ite_self]
theorem s819 (pattern : Ten) : d120 (change pattern 8 7) = d10 pattern := by
  change (if pattern.c then d118 (change pattern 8 7) else d117 (change pattern 8 7)) = d10 pattern
  rw [s818, s816]
  simp only [ite_self]
theorem s820 (pattern : Ten) : d121 (change pattern 8 7) = d484 pattern := by
  change (if pattern.e then d120 (change pattern 8 7) else d119 (change pattern 8 7)) = d484 pattern
  rw [s819, s813]
  rfl
theorem s821 (pattern : Ten) : d122 (change pattern 8 7) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 8 7) else d120 (change pattern 8 7)) = d10 pattern
  rw [s804, s819]
  simp only [ite_self]
theorem s822 (pattern : Ten) : d123 (change pattern 8 7) = d485 pattern := by
  change (if pattern.d then d122 (change pattern 8 7) else d121 (change pattern 8 7)) = d485 pattern
  rw [s821, s820]
  rfl
theorem s823 (pattern : Ten) : d1 (change pattern 8 7) = d1 pattern := by
  rfl
theorem s824 (pattern : Ten) : d171 (change pattern 8 7) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 8 7) else d0 (change pattern 8 7)) = d171 pattern
  rw [s823, s799]
  rfl
theorem s825 (pattern : Ten) : d3 (change pattern 8 7) = d3 pattern := by
  rfl
theorem s826 (pattern : Ten) : d172 (change pattern 8 7) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 8 7) else d2 (change pattern 8 7)) = d172 pattern
  rw [s825, s800]
  rfl
theorem s827 (pattern : Ten) : d174 (change pattern 8 7) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 8 7) else d171 (change pattern 8 7)) = d174 pattern
  rw [s826, s824]
  rfl
theorem s828 (pattern : Ten) : d267 (change pattern 8 7) = d174 pattern := by
  change d174 (change pattern 8 7) = d174 pattern
  exact s827 pattern
theorem s829 (pattern : Ten) : d268 (change pattern 8 7) = d10 pattern := by
  change d10 (change pattern 8 7) = d10 pattern
  exact s804 pattern
theorem s830 (pattern : Ten) : d271 (change pattern 8 7) = d488 pattern := by
  change (if pattern.g then d268 (change pattern 8 7) else d267 (change pattern 8 7)) = d488 pattern
  rw [s829, s828]
  rfl
theorem s831 (pattern : Ten) : d5 (change pattern 8 7) = d5 pattern := by
  rfl
theorem s832 (pattern : Ten) : d193 (change pattern 8 7) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 8 7) else d4 (change pattern 8 7)) = d193 pattern
  rw [s831, s809]
  rfl
theorem s833 (pattern : Ten) : d199 (change pattern 8 7) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 8 7) else d172 (change pattern 8 7)) = d199 pattern
  rw [s832, s826]
  rfl
theorem s834 (pattern : Ten) : d269 (change pattern 8 7) = d199 pattern := by
  change d199 (change pattern 8 7) = d199 pattern
  exact s833 pattern
theorem s835 (pattern : Ten) : d272 (change pattern 8 7) = d489 pattern := by
  change (if pattern.g then d268 (change pattern 8 7) else d269 (change pattern 8 7)) = d489 pattern
  rw [s829, s834]
  rfl
theorem s836 (pattern : Ten) : d275 (change pattern 8 7) = d490 pattern := by
  change (if pattern.c then d272 (change pattern 8 7) else d271 (change pattern 8 7)) = d490 pattern
  rw [s835, s830]
  rfl
theorem s837 (pattern : Ten) : d273 (change pattern 8 7) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 8 7) else d268 (change pattern 8 7)) = d10 pattern
  rw [s804, s829]
  simp only [ite_self]
theorem s838 (pattern : Ten) : d270 (change pattern 8 7) = d10 pattern := by
  change d10 (change pattern 8 7) = d10 pattern
  exact s804 pattern
theorem s839 (pattern : Ten) : d274 (change pattern 8 7) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 8 7) else d270 (change pattern 8 7)) = d10 pattern
  rw [s804, s838]
  simp only [ite_self]
theorem s840 (pattern : Ten) : d276 (change pattern 8 7) = d10 pattern := by
  change (if pattern.c then d274 (change pattern 8 7) else d273 (change pattern 8 7)) = d10 pattern
  rw [s839, s837]
  simp only [ite_self]
theorem s841 (pattern : Ten) : d277 (change pattern 8 7) = d491 pattern := by
  change (if pattern.e then d276 (change pattern 8 7) else d275 (change pattern 8 7)) = d491 pattern
  rw [s840, s836]
  rfl
theorem s842 (pattern : Ten) : d278 (change pattern 8 7) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 8 7) else d276 (change pattern 8 7)) = d10 pattern
  rw [s804, s840]
  simp only [ite_self]
theorem s843 (pattern : Ten) : d279 (change pattern 8 7) = d492 pattern := by
  change (if pattern.d then d278 (change pattern 8 7) else d277 (change pattern 8 7)) = d492 pattern
  rw [s842, s841]
  rfl
theorem s844 (pattern : Ten) : d2 (change pattern 8 9) = d2 pattern := by
  rfl
theorem s845 (pattern : Ten) : d15 (change pattern 8 9) = d2 pattern := by
  change d2 (change pattern 8 9) = d2 pattern
  exact s844 pattern
theorem s846 (pattern : Ten) : d108 (change pattern 8 9) = d2 pattern := by
  change d15 (change pattern 8 9) = d2 pattern
  exact s845 pattern
theorem s847 (pattern : Ten) : d109 (change pattern 8 9) = d2 pattern := by
  change (if pattern.h then d15 (change pattern 8 9) else d108 (change pattern 8 9)) = d2 pattern
  rw [s845, s846]
  simp only [ite_self]
theorem s848 (pattern : Ten) : d10 (change pattern 8 9) = d10 pattern := by
  rfl
theorem s849 (pattern : Ten) : d14 (change pattern 8 9) = d10 pattern := by
  change d10 (change pattern 8 9) = d10 pattern
  exact s848 pattern
theorem s850 (pattern : Ten) : d110 (change pattern 8 9) = d455 pattern := by
  change (if pattern.h then d14 (change pattern 8 9) else d15 (change pattern 8 9)) = d455 pattern
  rw [s849, s845]
  rfl
theorem s851 (pattern : Ten) : d115 (change pattern 8 9) = d495 pattern := by
  change (if pattern.g then d110 (change pattern 8 9) else d109 (change pattern 8 9)) = d495 pattern
  rw [s850, s847]
  rfl
theorem s852 (pattern : Ten) : d4 (change pattern 8 9) = d4 pattern := by
  rfl
theorem s853 (pattern : Ten) : d44 (change pattern 8 9) = d4 pattern := by
  change d4 (change pattern 8 9) = d4 pattern
  exact s852 pattern
theorem s854 (pattern : Ten) : d111 (change pattern 8 9) = d496 pattern := by
  change (if pattern.h then d44 (change pattern 8 9) else d15 (change pattern 8 9)) = d496 pattern
  rw [s853, s845]
  rfl
theorem s855 (pattern : Ten) : d116 (change pattern 8 9) = d497 pattern := by
  change (if pattern.g then d110 (change pattern 8 9) else d111 (change pattern 8 9)) = d497 pattern
  rw [s850, s854]
  rfl
theorem s856 (pattern : Ten) : d119 (change pattern 8 9) = d498 pattern := by
  change (if pattern.c then d116 (change pattern 8 9) else d115 (change pattern 8 9)) = d498 pattern
  rw [s855, s851]
  rfl
theorem s857 (pattern : Ten) : d112 (change pattern 8 9) = d455 pattern := by
  change (if pattern.h then d10 (change pattern 8 9) else d15 (change pattern 8 9)) = d455 pattern
  rw [s848, s845]
  rfl
theorem s858 (pattern : Ten) : d113 (change pattern 8 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 8 9) else d14 (change pattern 8 9)) = d10 pattern
  rw [s848, s849]
  simp only [ite_self]
theorem s859 (pattern : Ten) : d117 (change pattern 8 9) = d499 pattern := by
  change (if pattern.g then d113 (change pattern 8 9) else d112 (change pattern 8 9)) = d499 pattern
  rw [s858, s857]
  rfl
theorem s860 (pattern : Ten) : d114 (change pattern 8 9) = d500 pattern := by
  change (if pattern.h then d10 (change pattern 8 9) else d44 (change pattern 8 9)) = d500 pattern
  rw [s848, s853]
  rfl
theorem s861 (pattern : Ten) : d118 (change pattern 8 9) = d501 pattern := by
  change (if pattern.g then d113 (change pattern 8 9) else d114 (change pattern 8 9)) = d501 pattern
  rw [s858, s860]
  rfl
theorem s862 (pattern : Ten) : d120 (change pattern 8 9) = d502 pattern := by
  change (if pattern.c then d118 (change pattern 8 9) else d117 (change pattern 8 9)) = d502 pattern
  rw [s861, s859]
  rfl
theorem s863 (pattern : Ten) : d121 (change pattern 8 9) = d503 pattern := by
  change (if pattern.e then d120 (change pattern 8 9) else d119 (change pattern 8 9)) = d503 pattern
  rw [s862, s856]
  rfl
theorem s864 (pattern : Ten) : d122 (change pattern 8 9) = d504 pattern := by
  change (if pattern.e then d10 (change pattern 8 9) else d120 (change pattern 8 9)) = d504 pattern
  rw [s848, s862]
  rfl
theorem s865 (pattern : Ten) : d123 (change pattern 8 9) = d505 pattern := by
  change (if pattern.d then d122 (change pattern 8 9) else d121 (change pattern 8 9)) = d505 pattern
  rw [s864, s863]
  rfl
theorem s866 (pattern : Ten) : d3 (change pattern 8 9) = d3 pattern := by
  rfl
theorem s867 (pattern : Ten) : d172 (change pattern 8 9) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 8 9) else d2 (change pattern 8 9)) = d172 pattern
  rw [s866, s844]
  rfl
theorem s868 (pattern : Ten) : d174 (change pattern 8 9) = d172 pattern := by
  change d172 (change pattern 8 9) = d172 pattern
  exact s867 pattern
theorem s869 (pattern : Ten) : d266 (change pattern 8 9) = d172 pattern := by
  change d174 (change pattern 8 9) = d172 pattern
  exact s868 pattern
theorem s870 (pattern : Ten) : d267 (change pattern 8 9) = d172 pattern := by
  change (if pattern.h then d174 (change pattern 8 9) else d266 (change pattern 8 9)) = d172 pattern
  rw [s868, s869]
  simp only [ite_self]
theorem s871 (pattern : Ten) : d268 (change pattern 8 9) = d463 pattern := by
  change (if pattern.h then d10 (change pattern 8 9) else d174 (change pattern 8 9)) = d463 pattern
  rw [s848, s868]
  rfl
theorem s872 (pattern : Ten) : d271 (change pattern 8 9) = d507 pattern := by
  change (if pattern.g then d268 (change pattern 8 9) else d267 (change pattern 8 9)) = d507 pattern
  rw [s871, s870]
  rfl
theorem s873 (pattern : Ten) : d5 (change pattern 8 9) = d5 pattern := by
  rfl
theorem s874 (pattern : Ten) : d193 (change pattern 8 9) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 8 9) else d4 (change pattern 8 9)) = d193 pattern
  rw [s873, s852]
  rfl
theorem s875 (pattern : Ten) : d199 (change pattern 8 9) = d193 pattern := by
  change d193 (change pattern 8 9) = d193 pattern
  exact s874 pattern
theorem s876 (pattern : Ten) : d269 (change pattern 8 9) = d508 pattern := by
  change (if pattern.h then d199 (change pattern 8 9) else d174 (change pattern 8 9)) = d508 pattern
  rw [s875, s868]
  rfl
theorem s877 (pattern : Ten) : d272 (change pattern 8 9) = d509 pattern := by
  change (if pattern.g then d268 (change pattern 8 9) else d269 (change pattern 8 9)) = d509 pattern
  rw [s871, s876]
  rfl
theorem s878 (pattern : Ten) : d275 (change pattern 8 9) = d510 pattern := by
  change (if pattern.c then d272 (change pattern 8 9) else d271 (change pattern 8 9)) = d510 pattern
  rw [s877, s872]
  rfl
theorem s879 (pattern : Ten) : d273 (change pattern 8 9) = d464 pattern := by
  change (if pattern.g then d10 (change pattern 8 9) else d268 (change pattern 8 9)) = d464 pattern
  rw [s848, s871]
  rfl
theorem s880 (pattern : Ten) : d270 (change pattern 8 9) = d511 pattern := by
  change (if pattern.h then d10 (change pattern 8 9) else d199 (change pattern 8 9)) = d511 pattern
  rw [s848, s875]
  rfl
theorem s881 (pattern : Ten) : d274 (change pattern 8 9) = d512 pattern := by
  change (if pattern.g then d10 (change pattern 8 9) else d270 (change pattern 8 9)) = d512 pattern
  rw [s848, s880]
  rfl
theorem s882 (pattern : Ten) : d276 (change pattern 8 9) = d513 pattern := by
  change (if pattern.c then d274 (change pattern 8 9) else d273 (change pattern 8 9)) = d513 pattern
  rw [s881, s879]
  rfl
theorem s883 (pattern : Ten) : d277 (change pattern 8 9) = d514 pattern := by
  change (if pattern.e then d276 (change pattern 8 9) else d275 (change pattern 8 9)) = d514 pattern
  rw [s882, s878]
  rfl
theorem s884 (pattern : Ten) : d278 (change pattern 8 9) = d515 pattern := by
  change (if pattern.e then d10 (change pattern 8 9) else d276 (change pattern 8 9)) = d515 pattern
  rw [s848, s882]
  rfl
theorem s885 (pattern : Ten) : d279 (change pattern 8 9) = d516 pattern := by
  change (if pattern.d then d278 (change pattern 8 9) else d277 (change pattern 8 9)) = d516 pattern
  rw [s884, s883]
  rfl
theorem s886 (pattern : Ten) : d0 (change pattern 7 3) = d0 pattern := by
  rfl
theorem s887 (pattern : Ten) : d2 (change pattern 7 3) = d2 pattern := by
  rfl
theorem s888 (pattern : Ten) : d15 (change pattern 7 3) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 7 3) else d0 (change pattern 7 3)) = d15 pattern
  rw [s887, s886]
  rfl
theorem s889 (pattern : Ten) : d4 (change pattern 7 3) = d4 pattern := by
  rfl
theorem s890 (pattern : Ten) : d10 (change pattern 7 3) = d10 pattern := by
  rfl
theorem s891 (pattern : Ten) : d42 (change pattern 7 3) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 7 3) else d4 (change pattern 7 3)) = d42 pattern
  rw [s890, s889]
  rfl
theorem s892 (pattern : Ten) : d48 (change pattern 7 3) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 7 3) else d15 (change pattern 7 3)) = d48 pattern
  rw [s891, s888]
  rfl
theorem s893 (pattern : Ten) : d9 (change pattern 7 3) = d9 pattern := by
  rfl
theorem s894 (pattern : Ten) : d11 (change pattern 7 3) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 7 3) else d9 (change pattern 7 3)) = d11 pattern
  rw [s890, s893]
  rfl
theorem s895 (pattern : Ten) : d14 (change pattern 7 3) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 7 3) else d11 (change pattern 7 3)) = d14 pattern
  rw [s890, s894]
  rfl
theorem s896 (pattern : Ten) : d20 (change pattern 7 3) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 7 3) else d14 (change pattern 7 3)) = d20 pattern
  rw [s890, s895]
  rfl
theorem s897 (pattern : Ten) : d126 (change pattern 7 3) = d126 pattern := by
  change (if pattern.g then d20 (change pattern 7 3) else d48 (change pattern 7 3)) = d126 pattern
  rw [s896, s892]
  rfl
theorem s898 (pattern : Ten) : d44 (change pattern 7 3) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 7 3) else d2 (change pattern 7 3)) = d44 pattern
  rw [s889, s887]
  rfl
theorem s899 (pattern : Ten) : d6 (change pattern 7 3) = d6 pattern := by
  rfl
end NetHack.Sokoban41.Diagram
