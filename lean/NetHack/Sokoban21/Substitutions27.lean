/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions26
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4050 (pattern : Twelve) : d687 (change pattern 11 12) = d2757 pattern := by
  change (if pattern.h then d651 (change pattern 11 12) else d657 (change pattern 11 12)) = d2757 pattern
  rw [s4049, s4048]
  rfl
theorem s4051 (pattern : Twelve) : d1201 (change pattern 11 12) = d2758 pattern := by
  change (if pattern.f then d687 (change pattern 11 12) else d1192 (change pattern 11 12)) = d2758 pattern
  rw [s4050, s4047]
  rfl
theorem s4052 (pattern : Twelve) : d692 (change pattern 11 12) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 12) else d657 (change pattern 11 12)) = d56 pattern
  rw [s4046, s4048]
  rfl
theorem s4053 (pattern : Twelve) : d1202 (change pattern 11 12) = d2759 pattern := by
  change (if pattern.f then d1191 (change pattern 11 12) else d692 (change pattern 11 12)) = d2759 pattern
  rw [s4040, s4052]
  rfl
theorem s4054 (pattern : Twelve) : d1217 (change pattern 11 12) = d2760 pattern := by
  change (if pattern.e then d1202 (change pattern 11 12) else d1201 (change pattern 11 12)) = d2760 pattern
  rw [s4053, s4051]
  rfl
theorem s4055 (pattern : Twelve) : d1228 (change pattern 11 12) = d2761 pattern := by
  change (if pattern.j then d1217 (change pattern 11 12) else d1216 (change pattern 11 12)) = d2761 pattern
  rw [s4054, s4042]
  rfl
theorem s4056 (pattern : Twelve) : d659 (change pattern 11 12) = d0 pattern := by
  change (if pattern.i then d158 (change pattern 11 12) else d638 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4044]
  simp only [ite_self]
theorem s4057 (pattern : Twelve) : d690 (change pattern 11 12) = d0 pattern := by
  change (if pattern.h then d158 (change pattern 11 12) else d659 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4056]
  simp only [ite_self]
theorem s4058 (pattern : Twelve) : d661 (change pattern 11 12) = d26 pattern := by
  change (if pattern.i then d157 (change pattern 11 12) else d158 (change pattern 11 12)) = d26 pattern
  rw [s4025, s4018]
  rfl
theorem s4059 (pattern : Twelve) : d1193 (change pattern 11 12) = d2748 pattern := by
  change (if pattern.h then d1183 (change pattern 11 12) else d661 (change pattern 11 12)) = d2748 pattern
  rw [s4028, s4058]
  rfl
theorem s4060 (pattern : Twelve) : d1203 (change pattern 11 12) = d2749 pattern := by
  change (if pattern.f then d1193 (change pattern 11 12) else d690 (change pattern 11 12)) = d2749 pattern
  rw [s4059, s4057]
  rfl
theorem s4061 (pattern : Twelve) : d1204 (change pattern 11 12) = d2754 pattern := by
  change (if pattern.f then d1191 (change pattern 11 12) else d158 (change pattern 11 12)) = d2754 pattern
  rw [s4040, s4018]
  rfl
theorem s4062 (pattern : Twelve) : d1218 (change pattern 11 12) = d2755 pattern := by
  change (if pattern.e then d1204 (change pattern 11 12) else d1203 (change pattern 11 12)) = d2755 pattern
  rw [s4061, s4060]
  rfl
theorem s4063 (pattern : Twelve) : d716 (change pattern 11 12) = d2758 pattern := by
  change (if pattern.f then d687 (change pattern 11 12) else d692 (change pattern 11 12)) = d2758 pattern
  rw [s4050, s4052]
  rfl
theorem s4064 (pattern : Twelve) : d1219 (change pattern 11 12) = d2760 pattern := by
  change (if pattern.e then d1202 (change pattern 11 12) else d716 (change pattern 11 12)) = d2760 pattern
  rw [s4053, s4063]
  rfl
theorem s4065 (pattern : Twelve) : d1229 (change pattern 11 12) = d2761 pattern := by
  change (if pattern.j then d1219 (change pattern 11 12) else d1218 (change pattern 11 12)) = d2761 pattern
  rw [s4064, s4062]
  rfl
theorem s4066 (pattern : Twelve) : d1237 (change pattern 11 12) = d2761 pattern := by
  change (if pattern.d then d1229 (change pattern 11 12) else d1228 (change pattern 11 12)) = d2761 pattern
  rw [s4065, s4055]
  simp only [ite_self]
theorem s4067 (pattern : Twelve) : d630 (change pattern 11 12) = d0 pattern := by
  change d0 (change pattern 11 12) = d0 pattern
  exact s4016 pattern
theorem s4068 (pattern : Twelve) : d640 (change pattern 11 12) = d0 pattern := by
  change (if pattern.k then d158 (change pattern 11 12) else d630 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4067]
  simp only [ite_self]
theorem s4069 (pattern : Twelve) : d665 (change pattern 11 12) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 12) else d640 (change pattern 11 12)) = d30 pattern
  rw [s4033, s4068]
  rfl
theorem s4070 (pattern : Twelve) : d695 (change pattern 11 12) = d30 pattern := by
  change (if pattern.h then d657 (change pattern 11 12) else d665 (change pattern 11 12)) = d30 pattern
  rw [s4048, s4069]
  simp only [ite_self]
theorem s4071 (pattern : Twelve) : d1185 (change pattern 11 12) = d2762 pattern := by
  change (if pattern.i then d159 (change pattern 11 12) else d636 (change pattern 11 12)) = d2762 pattern
  rw [s4035, s4027]
  rfl
theorem s4072 (pattern : Twelve) : d1194 (change pattern 11 12) = d2763 pattern := by
  change (if pattern.h then d1185 (change pattern 11 12) else d657 (change pattern 11 12)) = d2763 pattern
  rw [s4071, s4048]
  rfl
theorem s4073 (pattern : Twelve) : d1205 (change pattern 11 12) = d2764 pattern := by
  change (if pattern.f then d1194 (change pattern 11 12) else d695 (change pattern 11 12)) = d2764 pattern
  rw [s4072, s4070]
  rfl
theorem s4074 (pattern : Twelve) : d1206 (change pattern 11 12) = d2765 pattern := by
  change (if pattern.f then d1191 (change pattern 11 12) else d657 (change pattern 11 12)) = d2765 pattern
  rw [s4040, s4048]
  rfl
theorem s4075 (pattern : Twelve) : d1220 (change pattern 11 12) = d2766 pattern := by
  change (if pattern.e then d1206 (change pattern 11 12) else d1205 (change pattern 11 12)) = d2766 pattern
  rw [s4074, s4073]
  rfl
theorem s4076 (pattern : Twelve) : d4 (change pattern 11 12) = d4 pattern := by
  rfl
theorem s4077 (pattern : Twelve) : d13 (change pattern 11 12) = d4 pattern := by
  change d4 (change pattern 11 12) = d4 pattern
  exact s4076 pattern
theorem s4078 (pattern : Twelve) : d669 (change pattern 11 12) = d38 pattern := by
  change (if pattern.i then d13 (change pattern 11 12) else d160 (change pattern 11 12)) = d38 pattern
  rw [s4077, s4033]
  rfl
theorem s4079 (pattern : Twelve) : d668 (change pattern 11 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d160 (change pattern 11 12)) = d39 pattern
  rw [s4038, s4033]
  rfl
theorem s4080 (pattern : Twelve) : d697 (change pattern 11 12) = d59 pattern := by
  change (if pattern.h then d668 (change pattern 11 12) else d669 (change pattern 11 12)) = d59 pattern
  rw [s4079, s4078]
  rfl
theorem s4081 (pattern : Twelve) : d698 (change pattern 11 12) = d2767 pattern := by
  change (if pattern.h then d670 (change pattern 11 12) else d669 (change pattern 11 12)) = d2767 pattern
  rw [s4039, s4078]
  rfl
theorem s4082 (pattern : Twelve) : d720 (change pattern 11 12) = d2768 pattern := by
  change (if pattern.f then d698 (change pattern 11 12) else d697 (change pattern 11 12)) = d2768 pattern
  rw [s4081, s4080]
  rfl
theorem s4083 (pattern : Twelve) : d5 (change pattern 11 12) = d5 pattern := by
  rfl
theorem s4084 (pattern : Twelve) : d14 (change pattern 11 12) = d5 pattern := by
  change d5 (change pattern 11 12) = d5 pattern
  exact s4083 pattern
theorem s4085 (pattern : Twelve) : d21 (change pattern 11 12) = d2769 pattern := by
  change (if pattern.k then d14 (change pattern 11 12) else d13 (change pattern 11 12)) = d2769 pattern
  rw [s4084, s4077]
  rfl
theorem s4086 (pattern : Twelve) : d1186 (change pattern 11 12) = d2770 pattern := by
  change (if pattern.i then d21 (change pattern 11 12) else d644 (change pattern 11 12)) = d2770 pattern
  rw [s4085, s4036]
  rfl
theorem s4087 (pattern : Twelve) : d822 (change pattern 11 12) = d2771 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d21 (change pattern 11 12)) = d2771 pattern
  rw [s4038, s4085]
  rfl
theorem s4088 (pattern : Twelve) : d1195 (change pattern 11 12) = d2772 pattern := by
  change (if pattern.h then d822 (change pattern 11 12) else d1186 (change pattern 11 12)) = d2772 pattern
  rw [s4087, s4086]
  rfl
theorem s4089 (pattern : Twelve) : d1207 (change pattern 11 12) = d2773 pattern := by
  change (if pattern.f then d1195 (change pattern 11 12) else d697 (change pattern 11 12)) = d2773 pattern
  rw [s4088, s4080]
  rfl
theorem s4090 (pattern : Twelve) : d1221 (change pattern 11 12) = d2774 pattern := by
  change (if pattern.e then d1207 (change pattern 11 12) else d720 (change pattern 11 12)) = d2774 pattern
  rw [s4089, s4082]
  rfl
theorem s4091 (pattern : Twelve) : d1230 (change pattern 11 12) = d2775 pattern := by
  change (if pattern.j then d1221 (change pattern 11 12) else d1220 (change pattern 11 12)) = d2775 pattern
  rw [s4090, s4075]
  rfl
theorem s4092 (pattern : Twelve) : d1231 (change pattern 11 12) = d2776 pattern := by
  change (if pattern.j then d6 (change pattern 11 12) else d1219 (change pattern 11 12)) = d2776 pattern
  rw [s4038, s4064]
  rfl
theorem s4093 (pattern : Twelve) : d1238 (change pattern 11 12) = d2777 pattern := by
  change (if pattern.d then d1231 (change pattern 11 12) else d1230 (change pattern 11 12)) = d2777 pattern
  rw [s4092, s4091]
  rfl
theorem s4094 (pattern : Twelve) : d1241 (change pattern 11 12) = d2778 pattern := by
  change (if pattern.c then d1238 (change pattern 11 12) else d1237 (change pattern 11 12)) = d2778 pattern
  rw [s4093, s4066]
  rfl
theorem s4095 (pattern : Twelve) : d1208 (change pattern 11 12) = d2749 pattern := by
  change (if pattern.f then d1193 (change pattern 11 12) else d158 (change pattern 11 12)) = d2749 pattern
  rw [s4059, s4018]
  rfl
theorem s4096 (pattern : Twelve) : d1222 (change pattern 11 12) = d2755 pattern := by
  change (if pattern.e then d1204 (change pattern 11 12) else d1208 (change pattern 11 12)) = d2755 pattern
  rw [s4061, s4095]
  rfl
theorem s4097 (pattern : Twelve) : d1232 (change pattern 11 12) = d2761 pattern := by
  change (if pattern.j then d1219 (change pattern 11 12) else d1222 (change pattern 11 12)) = d2761 pattern
  rw [s4064, s4096]
  rfl
theorem s4098 (pattern : Twelve) : d1209 (change pattern 11 12) = d2764 pattern := by
  change (if pattern.f then d1194 (change pattern 11 12) else d657 (change pattern 11 12)) = d2764 pattern
  rw [s4072, s4048]
  rfl
theorem s4099 (pattern : Twelve) : d1223 (change pattern 11 12) = d2766 pattern := by
  change (if pattern.e then d1206 (change pattern 11 12) else d1209 (change pattern 11 12)) = d2766 pattern
  rw [s4074, s4098]
  rfl
theorem s4100 (pattern : Twelve) : d1233 (change pattern 11 12) = d2775 pattern := by
  change (if pattern.j then d1221 (change pattern 11 12) else d1223 (change pattern 11 12)) = d2775 pattern
  rw [s4090, s4099]
  rfl
theorem s4101 (pattern : Twelve) : d1239 (change pattern 11 12) = d2777 pattern := by
  change (if pattern.d then d1231 (change pattern 11 12) else d1233 (change pattern 11 12)) = d2777 pattern
  rw [s4092, s4100]
  rfl
theorem s4102 (pattern : Twelve) : d1242 (change pattern 11 12) = d2778 pattern := by
  change (if pattern.c then d1239 (change pattern 11 12) else d1232 (change pattern 11 12)) = d2778 pattern
  rw [s4101, s4097]
  rfl
theorem s4103 (pattern : Twelve) : d1244 (change pattern 11 12) = d2778 pattern := by
  change (if pattern.g then d1242 (change pattern 11 12) else d1241 (change pattern 11 12)) = d2778 pattern
  rw [s4102, s4094]
  simp only [ite_self]
theorem s4104 (pattern : Twelve) : d1245 (change pattern 11 12) = d2778 pattern := by
  change (if pattern.b then d1242 (change pattern 11 12) else d1244 (change pattern 11 12)) = d2778 pattern
  rw [s4102, s4103]
  simp only [ite_self]
theorem s4105 (pattern : Twelve) : d1187 (change pattern 11 12) = d2779 pattern := by
  change (if pattern.i then d21 (change pattern 11 12) else d636 (change pattern 11 12)) = d2779 pattern
  rw [s4085, s4027]
  rfl
theorem s4106 (pattern : Twelve) : d1196 (change pattern 11 12) = d2780 pattern := by
  change (if pattern.h then d670 (change pattern 11 12) else d1187 (change pattern 11 12)) = d2780 pattern
  rw [s4039, s4105]
  rfl
theorem s4107 (pattern : Twelve) : d1210 (change pattern 11 12) = d2781 pattern := by
  change (if pattern.f then d1196 (change pattern 11 12) else d158 (change pattern 11 12)) = d2781 pattern
  rw [s4106, s4018]
  rfl
theorem s4108 (pattern : Twelve) : d1224 (change pattern 11 12) = d2782 pattern := by
  change (if pattern.e then d1210 (change pattern 11 12) else d1208 (change pattern 11 12)) = d2782 pattern
  rw [s4107, s4095]
  rfl
theorem s4109 (pattern : Twelve) : d674 (change pattern 11 12) = d2783 pattern := by
  change (if pattern.i then d644 (change pattern 11 12) else d158 (change pattern 11 12)) = d2783 pattern
  rw [s4036, s4018]
  rfl
theorem s4110 (pattern : Twelve) : d705 (change pattern 11 12) = d2784 pattern := by
  change (if pattern.h then d651 (change pattern 11 12) else d674 (change pattern 11 12)) = d2784 pattern
  rw [s4049, s4109]
  rfl
theorem s4111 (pattern : Twelve) : d731 (change pattern 11 12) = d2785 pattern := by
  change (if pattern.f then d705 (change pattern 11 12) else d692 (change pattern 11 12)) = d2785 pattern
  rw [s4110, s4052]
  rfl
theorem s4112 (pattern : Twelve) : d1211 (change pattern 11 12) = d2786 pattern := by
  change (if pattern.f then d1196 (change pattern 11 12) else d692 (change pattern 11 12)) = d2786 pattern
  rw [s4106, s4052]
  rfl
theorem s4113 (pattern : Twelve) : d1225 (change pattern 11 12) = d2787 pattern := by
  change (if pattern.e then d1211 (change pattern 11 12) else d731 (change pattern 11 12)) = d2787 pattern
  rw [s4112, s4111]
  rfl
theorem s4114 (pattern : Twelve) : d1234 (change pattern 11 12) = d2788 pattern := by
  change (if pattern.j then d1225 (change pattern 11 12) else d1224 (change pattern 11 12)) = d2788 pattern
  rw [s4113, s4108]
  rfl
theorem s4115 (pattern : Twelve) : d1188 (change pattern 11 12) = d2789 pattern := by
  change (if pattern.i then d13 (change pattern 11 12) else d636 (change pattern 11 12)) = d2789 pattern
  rw [s4077, s4027]
  rfl
theorem s4116 (pattern : Twelve) : d1197 (change pattern 11 12) = d2790 pattern := by
  change (if pattern.h then d1188 (change pattern 11 12) else d674 (change pattern 11 12)) = d2790 pattern
  rw [s4115, s4109]
  rfl
theorem s4117 (pattern : Twelve) : d1212 (change pattern 11 12) = d2791 pattern := by
  change (if pattern.f then d1197 (change pattern 11 12) else d657 (change pattern 11 12)) = d2791 pattern
  rw [s4116, s4048]
  rfl
theorem s4118 (pattern : Twelve) : d666 (change pattern 11 12) = d123 pattern := by
  change (if pattern.i then d159 (change pattern 11 12) else d158 (change pattern 11 12)) = d123 pattern
  rw [s4035, s4018]
  rfl
theorem s4119 (pattern : Twelve) : d704 (change pattern 11 12) = d132 pattern := by
  change (if pattern.h then d666 (change pattern 11 12) else d657 (change pattern 11 12)) = d132 pattern
  rw [s4118, s4048]
  rfl
theorem s4120 (pattern : Twelve) : d1213 (change pattern 11 12) = d2792 pattern := by
  change (if pattern.f then d1196 (change pattern 11 12) else d704 (change pattern 11 12)) = d2792 pattern
  rw [s4106, s4119]
  rfl
theorem s4121 (pattern : Twelve) : d1226 (change pattern 11 12) = d2793 pattern := by
  change (if pattern.e then d1213 (change pattern 11 12) else d1212 (change pattern 11 12)) = d2793 pattern
  rw [s4120, s4117]
  rfl
theorem s4122 (pattern : Twelve) : d22 (change pattern 11 12) = d497 pattern := by
  change (if pattern.k then d6 (change pattern 11 12) else d14 (change pattern 11 12)) = d497 pattern
  rw [s4038, s4084]
  rfl
theorem s4123 (pattern : Twelve) : d678 (change pattern 11 12) = d2794 pattern := by
  change (if pattern.i then d22 (change pattern 11 12) else d160 (change pattern 11 12)) = d2794 pattern
  rw [s4122, s4033]
  rfl
theorem s4124 (pattern : Twelve) : d639 (change pattern 11 12) = d2795 pattern := by
  change (if pattern.k then d13 (change pattern 11 12) else d159 (change pattern 11 12)) = d2795 pattern
  rw [s4077, s4035]
  rfl
theorem s4125 (pattern : Twelve) : d679 (change pattern 11 12) = d2796 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d639 (change pattern 11 12)) = d2796 pattern
  rw [s4038, s4124]
  rfl
theorem s4126 (pattern : Twelve) : d708 (change pattern 11 12) = d2797 pattern := by
  change (if pattern.h then d679 (change pattern 11 12) else d678 (change pattern 11 12)) = d2797 pattern
  rw [s4125, s4123]
  rfl
theorem s4127 (pattern : Twelve) : d1214 (change pattern 11 12) = d2798 pattern := by
  change (if pattern.f then d708 (change pattern 11 12) else d697 (change pattern 11 12)) = d2798 pattern
  rw [s4126, s4080]
  rfl
theorem s4128 (pattern : Twelve) : d676 (change pattern 11 12) = d126 pattern := by
  change (if pattern.i then d14 (change pattern 11 12) else d160 (change pattern 11 12)) = d126 pattern
  rw [s4084, s4033]
  rfl
theorem s4129 (pattern : Twelve) : d677 (change pattern 11 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d159 (change pattern 11 12)) = d47 pattern
  rw [s4038, s4035]
  rfl
theorem s4130 (pattern : Twelve) : d707 (change pattern 11 12) = d134 pattern := by
  change (if pattern.h then d677 (change pattern 11 12) else d676 (change pattern 11 12)) = d134 pattern
  rw [s4129, s4128]
  rfl
theorem s4131 (pattern : Twelve) : d1198 (change pattern 11 12) = d2799 pattern := by
  change (if pattern.h then d6 (change pattern 11 12) else d670 (change pattern 11 12)) = d2799 pattern
  rw [s4038, s4039]
  rfl
theorem s4132 (pattern : Twelve) : d1215 (change pattern 11 12) = d2800 pattern := by
  change (if pattern.f then d1198 (change pattern 11 12) else d707 (change pattern 11 12)) = d2800 pattern
  rw [s4131, s4130]
  rfl
theorem s4133 (pattern : Twelve) : d1227 (change pattern 11 12) = d2801 pattern := by
  change (if pattern.e then d1215 (change pattern 11 12) else d1214 (change pattern 11 12)) = d2801 pattern
  rw [s4132, s4127]
  rfl
theorem s4134 (pattern : Twelve) : d1235 (change pattern 11 12) = d2802 pattern := by
  change (if pattern.j then d1227 (change pattern 11 12) else d1226 (change pattern 11 12)) = d2802 pattern
  rw [s4133, s4121]
  rfl
theorem s4135 (pattern : Twelve) : d1236 (change pattern 11 12) = d2803 pattern := by
  change (if pattern.j then d6 (change pattern 11 12) else d1225 (change pattern 11 12)) = d2803 pattern
  rw [s4038, s4113]
  rfl
theorem s4136 (pattern : Twelve) : d1240 (change pattern 11 12) = d2804 pattern := by
  change (if pattern.d then d1236 (change pattern 11 12) else d1235 (change pattern 11 12)) = d2804 pattern
  rw [s4135, s4134]
  rfl
theorem s4137 (pattern : Twelve) : d1243 (change pattern 11 12) = d2805 pattern := by
  change (if pattern.c then d1240 (change pattern 11 12) else d1234 (change pattern 11 12)) = d2805 pattern
  rw [s4136, s4114]
  rfl
theorem s4138 (pattern : Twelve) : d1246 (change pattern 11 12) = d2806 pattern := by
  change (if pattern.a then d1243 (change pattern 11 12) else d1245 (change pattern 11 12)) = d2806 pattern
  rw [s4137, s4104]
  rfl
theorem s4139 (pattern : Twelve) : d1564 (change pattern 11 12) = d2807 pattern := by
  change (if pattern.h then d157 (change pattern 11 12) else d1183 (change pattern 11 12)) = d2807 pattern
  rw [s4025, s4028]
  rfl
theorem s4140 (pattern : Twelve) : d1576 (change pattern 11 12) = d2808 pattern := by
  change (if pattern.f then d1564 (change pattern 11 12) else d1190 (change pattern 11 12)) = d2808 pattern
  rw [s4139, s4031]
  rfl
theorem s4141 (pattern : Twelve) : d1577 (change pattern 11 12) = d2809 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d636 (change pattern 11 12)) = d2809 pattern
  rw [s4038, s4027]
  rfl
theorem s4142 (pattern : Twelve) : d1591 (change pattern 11 12) = d2810 pattern := by
  change (if pattern.e then d1577 (change pattern 11 12) else d1576 (change pattern 11 12)) = d2810 pattern
  rw [s4141, s4140]
  rfl
theorem s4143 (pattern : Twelve) : d1557 (change pattern 11 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d157 (change pattern 11 12)) = d45 pattern
  rw [s4038, s4025]
  rfl
theorem s4144 (pattern : Twelve) : d1565 (change pattern 11 12) = d2811 pattern := by
  change (if pattern.h then d1557 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2811 pattern
  rw [s4143, s4037]
  rfl
theorem s4145 (pattern : Twelve) : d1578 (change pattern 11 12) = d2812 pattern := by
  change (if pattern.f then d1565 (change pattern 11 12) else d692 (change pattern 11 12)) = d2812 pattern
  rw [s4144, s4052]
  rfl
theorem s4146 (pattern : Twelve) : d1566 (change pattern 11 12) = d2813 pattern := by
  change (if pattern.h then d651 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2813 pattern
  rw [s4049, s4037]
  rfl
theorem s4147 (pattern : Twelve) : d1579 (change pattern 11 12) = d2814 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1566 (change pattern 11 12)) = d2814 pattern
  rw [s4038, s4146]
  rfl
theorem s4148 (pattern : Twelve) : d1592 (change pattern 11 12) = d2815 pattern := by
  change (if pattern.e then d1579 (change pattern 11 12) else d1578 (change pattern 11 12)) = d2815 pattern
  rw [s4147, s4145]
  rfl
theorem s4149 (pattern : Twelve) : d1600 (change pattern 11 12) = d2816 pattern := by
  change (if pattern.j then d1592 (change pattern 11 12) else d1591 (change pattern 11 12)) = d2816 pattern
  rw [s4148, s4142]
  rfl
theorem s4150 (pattern : Twelve) : d1580 (change pattern 11 12) = d2808 pattern := by
  change (if pattern.f then d1564 (change pattern 11 12) else d158 (change pattern 11 12)) = d2808 pattern
  rw [s4139, s4018]
  rfl
theorem s4151 (pattern : Twelve) : d1593 (change pattern 11 12) = d2810 pattern := by
  change (if pattern.e then d1577 (change pattern 11 12) else d1580 (change pattern 11 12)) = d2810 pattern
  rw [s4141, s4150]
  rfl
theorem s4152 (pattern : Twelve) : d1601 (change pattern 11 12) = d2816 pattern := by
  change (if pattern.j then d1592 (change pattern 11 12) else d1593 (change pattern 11 12)) = d2816 pattern
  rw [s4148, s4151]
  rfl
theorem s4153 (pattern : Twelve) : d1607 (change pattern 11 12) = d2816 pattern := by
  change (if pattern.d then d1601 (change pattern 11 12) else d1600 (change pattern 11 12)) = d2816 pattern
  rw [s4152, s4149]
  simp only [ite_self]
theorem s4154 (pattern : Twelve) : d1558 (change pattern 11 12) = d46 pattern := by
  change (if pattern.i then d159 (change pattern 11 12) else d157 (change pattern 11 12)) = d46 pattern
  rw [s4035, s4025]
  rfl
theorem s4155 (pattern : Twelve) : d1567 (change pattern 11 12) = d2817 pattern := by
  change (if pattern.h then d1558 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2817 pattern
  rw [s4154, s4037]
  rfl
theorem s4156 (pattern : Twelve) : d1581 (change pattern 11 12) = d2818 pattern := by
  change (if pattern.f then d1567 (change pattern 11 12) else d657 (change pattern 11 12)) = d2818 pattern
  rw [s4155, s4048]
  rfl
theorem s4157 (pattern : Twelve) : d1582 (change pattern 11 12) = d2819 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2819 pattern
  rw [s4038, s4037]
  rfl
theorem s4158 (pattern : Twelve) : d1594 (change pattern 11 12) = d2820 pattern := by
  change (if pattern.e then d1582 (change pattern 11 12) else d1581 (change pattern 11 12)) = d2820 pattern
  rw [s4157, s4156]
  rfl
theorem s4159 (pattern : Twelve) : d1568 (change pattern 11 12) = d2821 pattern := by
  change (if pattern.h then d677 (change pattern 11 12) else d1186 (change pattern 11 12)) = d2821 pattern
  rw [s4129, s4086]
  rfl
theorem s4160 (pattern : Twelve) : d1583 (change pattern 11 12) = d2822 pattern := by
  change (if pattern.f then d1568 (change pattern 11 12) else d697 (change pattern 11 12)) = d2822 pattern
  rw [s4159, s4080]
  rfl
theorem s4161 (pattern : Twelve) : d1569 (change pattern 11 12) = d2823 pattern := by
  change (if pattern.h then d670 (change pattern 11 12) else d1186 (change pattern 11 12)) = d2823 pattern
  rw [s4039, s4086]
  rfl
theorem s4162 (pattern : Twelve) : d1584 (change pattern 11 12) = d2824 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1569 (change pattern 11 12)) = d2824 pattern
  rw [s4038, s4161]
  rfl
theorem s4163 (pattern : Twelve) : d1595 (change pattern 11 12) = d2825 pattern := by
  change (if pattern.e then d1584 (change pattern 11 12) else d1583 (change pattern 11 12)) = d2825 pattern
  rw [s4162, s4160]
  rfl
theorem s4164 (pattern : Twelve) : d1602 (change pattern 11 12) = d2826 pattern := by
  change (if pattern.j then d1595 (change pattern 11 12) else d1594 (change pattern 11 12)) = d2826 pattern
  rw [s4163, s4158]
  rfl
theorem s4165 (pattern : Twelve) : d1603 (change pattern 11 12) = d2827 pattern := by
  change (if pattern.j then d6 (change pattern 11 12) else d1592 (change pattern 11 12)) = d2827 pattern
  rw [s4038, s4148]
  rfl
theorem s4166 (pattern : Twelve) : d1608 (change pattern 11 12) = d2828 pattern := by
  change (if pattern.d then d1603 (change pattern 11 12) else d1602 (change pattern 11 12)) = d2828 pattern
  rw [s4165, s4164]
  rfl
theorem s4167 (pattern : Twelve) : d1610 (change pattern 11 12) = d2829 pattern := by
  change (if pattern.c then d1608 (change pattern 11 12) else d1607 (change pattern 11 12)) = d2829 pattern
  rw [s4166, s4153]
  rfl
theorem s4168 (pattern : Twelve) : d1611 (change pattern 11 12) = d2829 pattern := by
  change (if pattern.c then d1608 (change pattern 11 12) else d1601 (change pattern 11 12)) = d2829 pattern
  rw [s4166, s4152]
  rfl
theorem s4169 (pattern : Twelve) : d1613 (change pattern 11 12) = d2829 pattern := by
  change (if pattern.g then d1611 (change pattern 11 12) else d1610 (change pattern 11 12)) = d2829 pattern
  rw [s4168, s4167]
  simp only [ite_self]
theorem s4170 (pattern : Twelve) : d1614 (change pattern 11 12) = d2829 pattern := by
  change (if pattern.b then d1611 (change pattern 11 12) else d1613 (change pattern 11 12)) = d2829 pattern
  rw [s4168, s4169]
  simp only [ite_self]
theorem s4171 (pattern : Twelve) : d635 (change pattern 11 12) = d2830 pattern := by
  change (if pattern.k then d160 (change pattern 11 12) else d157 (change pattern 11 12)) = d2830 pattern
  rw [s4033, s4025]
  rfl
theorem s4172 (pattern : Twelve) : d1559 (change pattern 11 12) = d2831 pattern := by
  change (if pattern.i then d635 (change pattern 11 12) else d636 (change pattern 11 12)) = d2831 pattern
  rw [s4171, s4027]
  rfl
theorem s4173 (pattern : Twelve) : d1560 (change pattern 11 12) = d2832 pattern := by
  change (if pattern.i then d635 (change pattern 11 12) else d157 (change pattern 11 12)) = d2832 pattern
  rw [s4171, s4025]
  rfl
theorem s4174 (pattern : Twelve) : d1570 (change pattern 11 12) = d2833 pattern := by
  change (if pattern.h then d1560 (change pattern 11 12) else d1559 (change pattern 11 12)) = d2833 pattern
  rw [s4173, s4172]
  rfl
theorem s4175 (pattern : Twelve) : d1585 (change pattern 11 12) = d2834 pattern := by
  change (if pattern.f then d1570 (change pattern 11 12) else d158 (change pattern 11 12)) = d2834 pattern
  rw [s4174, s4018]
  rfl
theorem s4176 (pattern : Twelve) : d1596 (change pattern 11 12) = d2835 pattern := by
  change (if pattern.e then d1577 (change pattern 11 12) else d1585 (change pattern 11 12)) = d2835 pattern
  rw [s4141, s4175]
  rfl
theorem s4177 (pattern : Twelve) : d1571 (change pattern 11 12) = d2836 pattern := by
  change (if pattern.h then d1557 (change pattern 11 12) else d1185 (change pattern 11 12)) = d2836 pattern
  rw [s4143, s4071]
  rfl
theorem s4178 (pattern : Twelve) : d1586 (change pattern 11 12) = d2837 pattern := by
  change (if pattern.f then d1571 (change pattern 11 12) else d692 (change pattern 11 12)) = d2837 pattern
  rw [s4177, s4052]
  rfl
theorem s4179 (pattern : Twelve) : d1597 (change pattern 11 12) = d2838 pattern := by
  change (if pattern.e then d1579 (change pattern 11 12) else d1586 (change pattern 11 12)) = d2838 pattern
  rw [s4147, s4178]
  rfl
theorem s4180 (pattern : Twelve) : d1604 (change pattern 11 12) = d2839 pattern := by
  change (if pattern.j then d1597 (change pattern 11 12) else d1596 (change pattern 11 12)) = d2839 pattern
  rw [s4179, s4176]
  rfl
theorem s4181 (pattern : Twelve) : d1561 (change pattern 11 12) = d2840 pattern := by
  change (if pattern.i then d21 (change pattern 11 12) else d157 (change pattern 11 12)) = d2840 pattern
  rw [s4085, s4025]
  rfl
theorem s4182 (pattern : Twelve) : d1572 (change pattern 11 12) = d2841 pattern := by
  change (if pattern.h then d1561 (change pattern 11 12) else d1185 (change pattern 11 12)) = d2841 pattern
  rw [s4181, s4071]
  rfl
theorem s4183 (pattern : Twelve) : d1587 (change pattern 11 12) = d2842 pattern := by
  change (if pattern.f then d1572 (change pattern 11 12) else d657 (change pattern 11 12)) = d2842 pattern
  rw [s4182, s4048]
  rfl
theorem s4184 (pattern : Twelve) : d1562 (change pattern 11 12) = d2843 pattern := by
  change (if pattern.i then d639 (change pattern 11 12) else d636 (change pattern 11 12)) = d2843 pattern
  rw [s4124, s4027]
  rfl
theorem s4185 (pattern : Twelve) : d1573 (change pattern 11 12) = d2844 pattern := by
  change (if pattern.h then d1562 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2844 pattern
  rw [s4184, s4037]
  rfl
theorem s4186 (pattern : Twelve) : d1588 (change pattern 11 12) = d2845 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1573 (change pattern 11 12)) = d2845 pattern
  rw [s4038, s4185]
  rfl
theorem s4187 (pattern : Twelve) : d1598 (change pattern 11 12) = d2846 pattern := by
  change (if pattern.e then d1588 (change pattern 11 12) else d1587 (change pattern 11 12)) = d2846 pattern
  rw [s4186, s4183]
  rfl
theorem s4188 (pattern : Twelve) : d1574 (change pattern 11 12) = d2847 pattern := by
  change (if pattern.h then d822 (change pattern 11 12) else d670 (change pattern 11 12)) = d2847 pattern
  rw [s4087, s4039]
  rfl
theorem s4189 (pattern : Twelve) : d1589 (change pattern 11 12) = d2848 pattern := by
  change (if pattern.f then d1574 (change pattern 11 12) else d697 (change pattern 11 12)) = d2848 pattern
  rw [s4188, s4080]
  rfl
theorem s4190 (pattern : Twelve) : d1563 (change pattern 11 12) = d2849 pattern := by
  change (if pattern.i then d22 (change pattern 11 12) else d644 (change pattern 11 12)) = d2849 pattern
  rw [s4122, s4036]
  rfl
theorem s4191 (pattern : Twelve) : d1575 (change pattern 11 12) = d2850 pattern := by
  change (if pattern.h then d679 (change pattern 11 12) else d1563 (change pattern 11 12)) = d2850 pattern
  rw [s4125, s4190]
  rfl
theorem s4192 (pattern : Twelve) : d1590 (change pattern 11 12) = d2851 pattern := by
  change (if pattern.f then d6 (change pattern 11 12) else d1575 (change pattern 11 12)) = d2851 pattern
  rw [s4038, s4191]
  rfl
theorem s4193 (pattern : Twelve) : d1599 (change pattern 11 12) = d2852 pattern := by
  change (if pattern.e then d1590 (change pattern 11 12) else d1589 (change pattern 11 12)) = d2852 pattern
  rw [s4192, s4189]
  rfl
theorem s4194 (pattern : Twelve) : d1605 (change pattern 11 12) = d2853 pattern := by
  change (if pattern.j then d1599 (change pattern 11 12) else d1598 (change pattern 11 12)) = d2853 pattern
  rw [s4193, s4187]
  rfl
theorem s4195 (pattern : Twelve) : d1606 (change pattern 11 12) = d2854 pattern := by
  change (if pattern.j then d6 (change pattern 11 12) else d1597 (change pattern 11 12)) = d2854 pattern
  rw [s4038, s4179]
  rfl
theorem s4196 (pattern : Twelve) : d1609 (change pattern 11 12) = d2855 pattern := by
  change (if pattern.d then d1606 (change pattern 11 12) else d1605 (change pattern 11 12)) = d2855 pattern
  rw [s4195, s4194]
  rfl
theorem s4197 (pattern : Twelve) : d1612 (change pattern 11 12) = d2856 pattern := by
  change (if pattern.c then d1609 (change pattern 11 12) else d1604 (change pattern 11 12)) = d2856 pattern
  rw [s4196, s4180]
  rfl
theorem s4198 (pattern : Twelve) : d1615 (change pattern 11 12) = d2857 pattern := by
  change (if pattern.a then d1612 (change pattern 11 12) else d1614 (change pattern 11 12)) = d2857 pattern
  rw [s4197, s4170]
  rfl
theorem s4199 (pattern : Twelve) : d1788 (change pattern 11 12) = d2858 pattern := by
  change (if pattern.f then d635 (change pattern 11 12) else d636 (change pattern 11 12)) = d2858 pattern
  rw [s4171, s4027]
  rfl
end NetHack.Sokoban21.Diagram
