/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions28
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4350 (pattern : Twelve) : d702 (change pattern 11 10) = d2899 pattern := by
  change (if pattern.h then d655 (change pattern 11 10) else d657 (change pattern 11 10)) = d2899 pattern
  rw [s4277, s4283]
  rfl
theorem s4351 (pattern : Twelve) : d724 (change pattern 11 10) = d2900 pattern := by
  change (if pattern.f then d702 (change pattern 11 10) else d701 (change pattern 11 10)) = d2900 pattern
  rw [s4350, s4349]
  rfl
theorem s4352 (pattern : Twelve) : d703 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d656 (change pattern 11 10) else d657 (change pattern 11 10)) = d56 pattern
  rw [s4281, s4283]
  rfl
theorem s4353 (pattern : Twelve) : d725 (change pattern 11 10) = d85 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d703 (change pattern 11 10)) = d85 pattern
  rw [s4284, s4352]
  rfl
theorem s4354 (pattern : Twelve) : d744 (change pattern 11 10) = d2901 pattern := by
  change (if pattern.e then d725 (change pattern 11 10) else d724 (change pattern 11 10)) = d2901 pattern
  rw [s4353, s4351]
  rfl
theorem s4355 (pattern : Twelve) : d758 (change pattern 11 10) = d2902 pattern := by
  change (if pattern.j then d744 (change pattern 11 10) else d743 (change pattern 11 10)) = d2902 pattern
  rw [s4354, s4347]
  rfl
theorem s4356 (pattern : Twelve) : d726 (change pattern 11 10) = d2896 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d158 (change pattern 11 10)) = d2896 pattern
  rw [s4284, s4240]
  rfl
theorem s4357 (pattern : Twelve) : d745 (change pattern 11 10) = d2897 pattern := by
  change (if pattern.e then d726 (change pattern 11 10) else d722 (change pattern 11 10)) = d2897 pattern
  rw [s4356, s4343]
  rfl
theorem s4358 (pattern : Twelve) : d746 (change pattern 11 10) = d2903 pattern := by
  change (if pattern.e then d716 (change pattern 11 10) else d692 (change pattern 11 10)) = d2903 pattern
  rw [s4305, s4303]
  rfl
theorem s4359 (pattern : Twelve) : d759 (change pattern 11 10) = d2904 pattern := by
  change (if pattern.j then d746 (change pattern 11 10) else d745 (change pattern 11 10)) = d2904 pattern
  rw [s4358, s4357]
  rfl
theorem s4360 (pattern : Twelve) : d768 (change pattern 11 10) = d2905 pattern := by
  change (if pattern.d then d759 (change pattern 11 10) else d758 (change pattern 11 10)) = d2905 pattern
  rw [s4359, s4355]
  rfl
theorem s4361 (pattern : Twelve) : d704 (change pattern 11 10) = d132 pattern := by
  change (if pattern.h then d666 (change pattern 11 10) else d657 (change pattern 11 10)) = d132 pattern
  rw [s4316, s4283]
  rfl
theorem s4362 (pattern : Twelve) : d727 (change pattern 11 10) = d2614 pattern := by
  change (if pattern.f then d704 (change pattern 11 10) else d657 (change pattern 11 10)) = d2614 pattern
  rw [s4361, s4283]
  rfl
theorem s4363 (pattern : Twelve) : d728 (change pattern 11 10) = d2906 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d657 (change pattern 11 10)) = d2906 pattern
  rw [s4284, s4283]
  rfl
theorem s4364 (pattern : Twelve) : d747 (change pattern 11 10) = d2907 pattern := by
  change (if pattern.e then d728 (change pattern 11 10) else d727 (change pattern 11 10)) = d2907 pattern
  rw [s4363, s4362]
  rfl
theorem s4365 (pattern : Twelve) : d748 (change pattern 11 10) = d2908 pattern := by
  change (if pattern.e then d720 (change pattern 11 10) else d697 (change pattern 11 10)) = d2908 pattern
  rw [s4332, s4327]
  rfl
theorem s4366 (pattern : Twelve) : d760 (change pattern 11 10) = d2909 pattern := by
  change (if pattern.j then d748 (change pattern 11 10) else d747 (change pattern 11 10)) = d2909 pattern
  rw [s4365, s4364]
  rfl
theorem s4367 (pattern : Twelve) : d761 (change pattern 11 10) = d2910 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d746 (change pattern 11 10)) = d2910 pattern
  rw [s4259, s4358]
  rfl
theorem s4368 (pattern : Twelve) : d769 (change pattern 11 10) = d2911 pattern := by
  change (if pattern.d then d761 (change pattern 11 10) else d760 (change pattern 11 10)) = d2911 pattern
  rw [s4367, s4366]
  rfl
theorem s4369 (pattern : Twelve) : d773 (change pattern 11 10) = d2912 pattern := by
  change (if pattern.c then d769 (change pattern 11 10) else d768 (change pattern 11 10)) = d2912 pattern
  rw [s4368, s4360]
  rfl
theorem s4370 (pattern : Twelve) : d775 (change pattern 11 10) = d2912 pattern := by
  change (if pattern.g then d773 (change pattern 11 10) else d772 (change pattern 11 10)) = d2912 pattern
  rw [s4369, s4342]
  simp only [ite_self]
theorem s4371 (pattern : Twelve) : d776 (change pattern 11 10) = d2912 pattern := by
  change (if pattern.b then d773 (change pattern 11 10) else d775 (change pattern 11 10)) = d2912 pattern
  rw [s4369, s4370]
  simp only [ite_self]
theorem s4372 (pattern : Twelve) : d674 (change pattern 11 10) = d123 pattern := by
  change (if pattern.i then d644 (change pattern 11 10) else d158 (change pattern 11 10)) = d123 pattern
  rw [s4329, s4240]
  rfl
theorem s4373 (pattern : Twelve) : d705 (change pattern 11 10) = d2913 pattern := by
  change (if pattern.h then d651 (change pattern 11 10) else d674 (change pattern 11 10)) = d2913 pattern
  rw [s4260, s4372]
  rfl
theorem s4374 (pattern : Twelve) : d729 (change pattern 11 10) = d2914 pattern := by
  change (if pattern.f then d705 (change pattern 11 10) else d158 (change pattern 11 10)) = d2914 pattern
  rw [s4373, s4240]
  rfl
theorem s4375 (pattern : Twelve) : d749 (change pattern 11 10) = d2915 pattern := by
  change (if pattern.e then d729 (change pattern 11 10) else d722 (change pattern 11 10)) = d2915 pattern
  rw [s4374, s4343]
  rfl
theorem s4376 (pattern : Twelve) : d730 (change pattern 11 10) = d2916 pattern := by
  change (if pattern.f then d692 (change pattern 11 10) else d701 (change pattern 11 10)) = d2916 pattern
  rw [s4303, s4349]
  rfl
theorem s4377 (pattern : Twelve) : d731 (change pattern 11 10) = d2917 pattern := by
  change (if pattern.f then d705 (change pattern 11 10) else d692 (change pattern 11 10)) = d2917 pattern
  rw [s4373, s4303]
  rfl
theorem s4378 (pattern : Twelve) : d750 (change pattern 11 10) = d2918 pattern := by
  change (if pattern.e then d731 (change pattern 11 10) else d730 (change pattern 11 10)) = d2918 pattern
  rw [s4377, s4376]
  rfl
theorem s4379 (pattern : Twelve) : d762 (change pattern 11 10) = d2919 pattern := by
  change (if pattern.j then d750 (change pattern 11 10) else d749 (change pattern 11 10)) = d2919 pattern
  rw [s4378, s4375]
  rfl
theorem s4380 (pattern : Twelve) : d751 (change pattern 11 10) = d2920 pattern := by
  change (if pattern.e then d731 (change pattern 11 10) else d692 (change pattern 11 10)) = d2920 pattern
  rw [s4377, s4303]
  rfl
theorem s4381 (pattern : Twelve) : d763 (change pattern 11 10) = d2921 pattern := by
  change (if pattern.j then d751 (change pattern 11 10) else d749 (change pattern 11 10)) = d2921 pattern
  rw [s4380, s4375]
  rfl
theorem s4382 (pattern : Twelve) : d770 (change pattern 11 10) = d2922 pattern := by
  change (if pattern.d then d763 (change pattern 11 10) else d762 (change pattern 11 10)) = d2922 pattern
  rw [s4381, s4379]
  rfl
theorem s4383 (pattern : Twelve) : d675 (change pattern 11 10) = d2635 pattern := by
  change (if pattern.i then d13 (change pattern 11 10) else d158 (change pattern 11 10)) = d2635 pattern
  rw [s4269, s4240]
  rfl
theorem s4384 (pattern : Twelve) : d706 (change pattern 11 10) = d2636 pattern := by
  change (if pattern.h then d675 (change pattern 11 10) else d657 (change pattern 11 10)) = d2636 pattern
  rw [s4383, s4283]
  rfl
theorem s4385 (pattern : Twelve) : d732 (change pattern 11 10) = d2637 pattern := by
  change (if pattern.f then d706 (change pattern 11 10) else d657 (change pattern 11 10)) = d2637 pattern
  rw [s4384, s4283]
  rfl
theorem s4386 (pattern : Twelve) : d733 (change pattern 11 10) = d2923 pattern := by
  change (if pattern.f then d705 (change pattern 11 10) else d704 (change pattern 11 10)) = d2923 pattern
  rw [s4373, s4361]
  rfl
theorem s4387 (pattern : Twelve) : d752 (change pattern 11 10) = d2924 pattern := by
  change (if pattern.e then d733 (change pattern 11 10) else d732 (change pattern 11 10)) = d2924 pattern
  rw [s4386, s4385]
  rfl
theorem s4388 (pattern : Twelve) : d676 (change pattern 11 10) = d126 pattern := by
  change (if pattern.i then d14 (change pattern 11 10) else d160 (change pattern 11 10)) = d126 pattern
  rw [s4275, s4255]
  rfl
theorem s4389 (pattern : Twelve) : d677 (change pattern 11 10) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d159 (change pattern 11 10)) = d47 pattern
  rw [s4259, s4315]
  rfl
theorem s4390 (pattern : Twelve) : d707 (change pattern 11 10) = d134 pattern := by
  change (if pattern.h then d677 (change pattern 11 10) else d676 (change pattern 11 10)) = d134 pattern
  rw [s4389, s4388]
  rfl
theorem s4391 (pattern : Twelve) : d734 (change pattern 11 10) = d2640 pattern := by
  change (if pattern.f then d707 (change pattern 11 10) else d697 (change pattern 11 10)) = d2640 pattern
  rw [s4390, s4327]
  rfl
theorem s4392 (pattern : Twelve) : d678 (change pattern 11 10) = d39 pattern := by
  change (if pattern.i then d22 (change pattern 11 10) else d160 (change pattern 11 10)) = d39 pattern
  rw [s4280, s4255]
  rfl
theorem s4393 (pattern : Twelve) : d679 (change pattern 11 10) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d639 (change pattern 11 10)) = d48 pattern
  rw [s4259, s4270]
  rfl
theorem s4394 (pattern : Twelve) : d708 (change pattern 11 10) = d2925 pattern := by
  change (if pattern.h then d679 (change pattern 11 10) else d678 (change pattern 11 10)) = d2925 pattern
  rw [s4393, s4392]
  rfl
theorem s4395 (pattern : Twelve) : d735 (change pattern 11 10) = d2926 pattern := by
  change (if pattern.f then d708 (change pattern 11 10) else d707 (change pattern 11 10)) = d2926 pattern
  rw [s4394, s4390]
  rfl
theorem s4396 (pattern : Twelve) : d753 (change pattern 11 10) = d2927 pattern := by
  change (if pattern.e then d735 (change pattern 11 10) else d734 (change pattern 11 10)) = d2927 pattern
  rw [s4395, s4391]
  rfl
theorem s4397 (pattern : Twelve) : d764 (change pattern 11 10) = d2928 pattern := by
  change (if pattern.j then d753 (change pattern 11 10) else d752 (change pattern 11 10)) = d2928 pattern
  rw [s4396, s4387]
  rfl
theorem s4398 (pattern : Twelve) : d765 (change pattern 11 10) = d2929 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d751 (change pattern 11 10)) = d2929 pattern
  rw [s4259, s4380]
  rfl
theorem s4399 (pattern : Twelve) : d771 (change pattern 11 10) = d2930 pattern := by
  change (if pattern.d then d765 (change pattern 11 10) else d764 (change pattern 11 10)) = d2930 pattern
  rw [s4398, s4397]
  rfl
theorem s4400 (pattern : Twelve) : d774 (change pattern 11 10) = d2931 pattern := by
  change (if pattern.c then d771 (change pattern 11 10) else d770 (change pattern 11 10)) = d2931 pattern
  rw [s4399, s4382]
  rfl
theorem s4401 (pattern : Twelve) : d777 (change pattern 11 10) = d2932 pattern := by
  change (if pattern.a then d774 (change pattern 11 10) else d776 (change pattern 11 10)) = d2932 pattern
  rw [s4400, s4371]
  rfl
theorem s4402 (pattern : Twelve) : d1183 (change pattern 11 10) = d1 pattern := by
  change (if pattern.i then d157 (change pattern 11 10) else d636 (change pattern 11 10)) = d1 pattern
  rw [s4245, s4258]
  simp only [ite_self]
theorem s4403 (pattern : Twelve) : d1189 (change pattern 11 10) = d2933 pattern := by
  change (if pattern.h then d1183 (change pattern 11 10) else d648 (change pattern 11 10)) = d2933 pattern
  rw [s4402, s4249]
  rfl
theorem s4404 (pattern : Twelve) : d1199 (change pattern 11 10) = d2934 pattern := by
  change (if pattern.f then d1189 (change pattern 11 10) else d682 (change pattern 11 10)) = d2934 pattern
  rw [s4403, s4253]
  rfl
theorem s4405 (pattern : Twelve) : d1190 (change pattern 11 10) = d0 pattern := by
  change (if pattern.h then d158 (change pattern 11 10) else d649 (change pattern 11 10)) = d0 pattern
  rw [s4240, s4252]
  simp only [ite_self]
theorem s4406 (pattern : Twelve) : d1184 (change pattern 11 10) = d46 pattern := by
  change (if pattern.i then d644 (change pattern 11 10) else d636 (change pattern 11 10)) = d46 pattern
  rw [s4329, s4258]
  rfl
theorem s4407 (pattern : Twelve) : d1191 (change pattern 11 10) = d2935 pattern := by
  change (if pattern.h then d670 (change pattern 11 10) else d1184 (change pattern 11 10)) = d2935 pattern
  rw [s4330, s4406]
  rfl
theorem s4408 (pattern : Twelve) : d1200 (change pattern 11 10) = d2936 pattern := by
  change (if pattern.f then d1191 (change pattern 11 10) else d1190 (change pattern 11 10)) = d2936 pattern
  rw [s4407, s4405]
  rfl
theorem s4409 (pattern : Twelve) : d1216 (change pattern 11 10) = d2937 pattern := by
  change (if pattern.e then d1200 (change pattern 11 10) else d1199 (change pattern 11 10)) = d2937 pattern
  rw [s4408, s4404]
  rfl
theorem s4410 (pattern : Twelve) : d1192 (change pattern 11 10) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 10) else d654 (change pattern 11 10)) = d56 pattern
  rw [s4301, s4273]
  rfl
theorem s4411 (pattern : Twelve) : d1201 (change pattern 11 10) = d85 pattern := by
  change (if pattern.f then d687 (change pattern 11 10) else d1192 (change pattern 11 10)) = d85 pattern
  rw [s4284, s4410]
  rfl
theorem s4412 (pattern : Twelve) : d1202 (change pattern 11 10) = d2938 pattern := by
  change (if pattern.f then d1191 (change pattern 11 10) else d692 (change pattern 11 10)) = d2938 pattern
  rw [s4407, s4303]
  rfl
theorem s4413 (pattern : Twelve) : d1217 (change pattern 11 10) = d2939 pattern := by
  change (if pattern.e then d1202 (change pattern 11 10) else d1201 (change pattern 11 10)) = d2939 pattern
  rw [s4412, s4411]
  rfl
theorem s4414 (pattern : Twelve) : d1228 (change pattern 11 10) = d2940 pattern := by
  change (if pattern.j then d1217 (change pattern 11 10) else d1216 (change pattern 11 10)) = d2940 pattern
  rw [s4413, s4409]
  rfl
theorem s4415 (pattern : Twelve) : d1193 (change pattern 11 10) = d2933 pattern := by
  change (if pattern.h then d1183 (change pattern 11 10) else d661 (change pattern 11 10)) = d2933 pattern
  rw [s4402, s4293]
  rfl
theorem s4416 (pattern : Twelve) : d1203 (change pattern 11 10) = d2934 pattern := by
  change (if pattern.f then d1193 (change pattern 11 10) else d690 (change pattern 11 10)) = d2934 pattern
  rw [s4415, s4296]
  rfl
theorem s4417 (pattern : Twelve) : d1204 (change pattern 11 10) = d2936 pattern := by
  change (if pattern.f then d1191 (change pattern 11 10) else d158 (change pattern 11 10)) = d2936 pattern
  rw [s4407, s4240]
  rfl
theorem s4418 (pattern : Twelve) : d1218 (change pattern 11 10) = d2937 pattern := by
  change (if pattern.e then d1204 (change pattern 11 10) else d1203 (change pattern 11 10)) = d2937 pattern
  rw [s4417, s4416]
  rfl
theorem s4419 (pattern : Twelve) : d1219 (change pattern 11 10) = d2939 pattern := by
  change (if pattern.e then d1202 (change pattern 11 10) else d716 (change pattern 11 10)) = d2939 pattern
  rw [s4412, s4305]
  rfl
theorem s4420 (pattern : Twelve) : d1229 (change pattern 11 10) = d2940 pattern := by
  change (if pattern.j then d1219 (change pattern 11 10) else d1218 (change pattern 11 10)) = d2940 pattern
  rw [s4419, s4418]
  rfl
theorem s4421 (pattern : Twelve) : d1237 (change pattern 11 10) = d2940 pattern := by
  change (if pattern.d then d1229 (change pattern 11 10) else d1228 (change pattern 11 10)) = d2940 pattern
  rw [s4420, s4414]
  simp only [ite_self]
theorem s4422 (pattern : Twelve) : d1185 (change pattern 11 10) = d46 pattern := by
  change (if pattern.i then d159 (change pattern 11 10) else d636 (change pattern 11 10)) = d46 pattern
  rw [s4315, s4258]
  rfl
theorem s4423 (pattern : Twelve) : d1194 (change pattern 11 10) = d67 pattern := by
  change (if pattern.h then d1185 (change pattern 11 10) else d657 (change pattern 11 10)) = d67 pattern
  rw [s4422, s4283]
  rfl
theorem s4424 (pattern : Twelve) : d1205 (change pattern 11 10) = d87 pattern := by
  change (if pattern.f then d1194 (change pattern 11 10) else d695 (change pattern 11 10)) = d87 pattern
  rw [s4423, s4319]
  rfl
theorem s4425 (pattern : Twelve) : d1206 (change pattern 11 10) = d2941 pattern := by
  change (if pattern.f then d1191 (change pattern 11 10) else d657 (change pattern 11 10)) = d2941 pattern
  rw [s4407, s4283]
  rfl
theorem s4426 (pattern : Twelve) : d1220 (change pattern 11 10) = d2942 pattern := by
  change (if pattern.e then d1206 (change pattern 11 10) else d1205 (change pattern 11 10)) = d2942 pattern
  rw [s4425, s4424]
  rfl
theorem s4427 (pattern : Twelve) : d1186 (change pattern 11 10) = d780 pattern := by
  change (if pattern.i then d21 (change pattern 11 10) else d644 (change pattern 11 10)) = d780 pattern
  rw [s4276, s4329]
  rfl
theorem s4428 (pattern : Twelve) : d822 (change pattern 11 10) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d21 (change pattern 11 10)) = d781 pattern
  rw [s4259, s4276]
  rfl
theorem s4429 (pattern : Twelve) : d1195 (change pattern 11 10) = d2943 pattern := by
  change (if pattern.h then d822 (change pattern 11 10) else d1186 (change pattern 11 10)) = d2943 pattern
  rw [s4428, s4427]
  rfl
theorem s4430 (pattern : Twelve) : d1207 (change pattern 11 10) = d2944 pattern := by
  change (if pattern.f then d1195 (change pattern 11 10) else d697 (change pattern 11 10)) = d2944 pattern
  rw [s4429, s4327]
  rfl
theorem s4431 (pattern : Twelve) : d1221 (change pattern 11 10) = d2945 pattern := by
  change (if pattern.e then d1207 (change pattern 11 10) else d720 (change pattern 11 10)) = d2945 pattern
  rw [s4430, s4332]
  rfl
theorem s4432 (pattern : Twelve) : d1230 (change pattern 11 10) = d2946 pattern := by
  change (if pattern.j then d1221 (change pattern 11 10) else d1220 (change pattern 11 10)) = d2946 pattern
  rw [s4431, s4426]
  rfl
theorem s4433 (pattern : Twelve) : d1231 (change pattern 11 10) = d2947 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d1219 (change pattern 11 10)) = d2947 pattern
  rw [s4259, s4419]
  rfl
theorem s4434 (pattern : Twelve) : d1238 (change pattern 11 10) = d2948 pattern := by
  change (if pattern.d then d1231 (change pattern 11 10) else d1230 (change pattern 11 10)) = d2948 pattern
  rw [s4433, s4432]
  rfl
theorem s4435 (pattern : Twelve) : d1241 (change pattern 11 10) = d2949 pattern := by
  change (if pattern.c then d1238 (change pattern 11 10) else d1237 (change pattern 11 10)) = d2949 pattern
  rw [s4434, s4421]
  rfl
theorem s4436 (pattern : Twelve) : d1208 (change pattern 11 10) = d2934 pattern := by
  change (if pattern.f then d1193 (change pattern 11 10) else d158 (change pattern 11 10)) = d2934 pattern
  rw [s4415, s4240]
  rfl
theorem s4437 (pattern : Twelve) : d1222 (change pattern 11 10) = d2937 pattern := by
  change (if pattern.e then d1204 (change pattern 11 10) else d1208 (change pattern 11 10)) = d2937 pattern
  rw [s4417, s4436]
  rfl
theorem s4438 (pattern : Twelve) : d1232 (change pattern 11 10) = d2940 pattern := by
  change (if pattern.j then d1219 (change pattern 11 10) else d1222 (change pattern 11 10)) = d2940 pattern
  rw [s4419, s4437]
  rfl
theorem s4439 (pattern : Twelve) : d1209 (change pattern 11 10) = d87 pattern := by
  change (if pattern.f then d1194 (change pattern 11 10) else d657 (change pattern 11 10)) = d87 pattern
  rw [s4423, s4283]
  rfl
theorem s4440 (pattern : Twelve) : d1223 (change pattern 11 10) = d2942 pattern := by
  change (if pattern.e then d1206 (change pattern 11 10) else d1209 (change pattern 11 10)) = d2942 pattern
  rw [s4425, s4439]
  rfl
theorem s4441 (pattern : Twelve) : d1233 (change pattern 11 10) = d2946 pattern := by
  change (if pattern.j then d1221 (change pattern 11 10) else d1223 (change pattern 11 10)) = d2946 pattern
  rw [s4431, s4440]
  rfl
theorem s4442 (pattern : Twelve) : d1239 (change pattern 11 10) = d2948 pattern := by
  change (if pattern.d then d1231 (change pattern 11 10) else d1233 (change pattern 11 10)) = d2948 pattern
  rw [s4433, s4441]
  rfl
theorem s4443 (pattern : Twelve) : d1242 (change pattern 11 10) = d2949 pattern := by
  change (if pattern.c then d1239 (change pattern 11 10) else d1232 (change pattern 11 10)) = d2949 pattern
  rw [s4442, s4438]
  rfl
theorem s4444 (pattern : Twelve) : d1244 (change pattern 11 10) = d2949 pattern := by
  change (if pattern.g then d1242 (change pattern 11 10) else d1241 (change pattern 11 10)) = d2949 pattern
  rw [s4443, s4435]
  simp only [ite_self]
theorem s4445 (pattern : Twelve) : d1245 (change pattern 11 10) = d2949 pattern := by
  change (if pattern.b then d1242 (change pattern 11 10) else d1244 (change pattern 11 10)) = d2949 pattern
  rw [s4443, s4444]
  simp only [ite_self]
theorem s4446 (pattern : Twelve) : d1187 (change pattern 11 10) = d2950 pattern := by
  change (if pattern.i then d21 (change pattern 11 10) else d636 (change pattern 11 10)) = d2950 pattern
  rw [s4276, s4258]
  rfl
theorem s4447 (pattern : Twelve) : d1196 (change pattern 11 10) = d2951 pattern := by
  change (if pattern.h then d670 (change pattern 11 10) else d1187 (change pattern 11 10)) = d2951 pattern
  rw [s4330, s4446]
  rfl
theorem s4448 (pattern : Twelve) : d1210 (change pattern 11 10) = d2952 pattern := by
  change (if pattern.f then d1196 (change pattern 11 10) else d158 (change pattern 11 10)) = d2952 pattern
  rw [s4447, s4240]
  rfl
theorem s4449 (pattern : Twelve) : d1224 (change pattern 11 10) = d2953 pattern := by
  change (if pattern.e then d1210 (change pattern 11 10) else d1208 (change pattern 11 10)) = d2953 pattern
  rw [s4448, s4436]
  rfl
theorem s4450 (pattern : Twelve) : d1211 (change pattern 11 10) = d2954 pattern := by
  change (if pattern.f then d1196 (change pattern 11 10) else d692 (change pattern 11 10)) = d2954 pattern
  rw [s4447, s4303]
  rfl
theorem s4451 (pattern : Twelve) : d1225 (change pattern 11 10) = d2955 pattern := by
  change (if pattern.e then d1211 (change pattern 11 10) else d731 (change pattern 11 10)) = d2955 pattern
  rw [s4450, s4377]
  rfl
theorem s4452 (pattern : Twelve) : d1234 (change pattern 11 10) = d2956 pattern := by
  change (if pattern.j then d1225 (change pattern 11 10) else d1224 (change pattern 11 10)) = d2956 pattern
  rw [s4451, s4449]
  rfl
theorem s4453 (pattern : Twelve) : d1188 (change pattern 11 10) = d2957 pattern := by
  change (if pattern.i then d13 (change pattern 11 10) else d636 (change pattern 11 10)) = d2957 pattern
  rw [s4269, s4258]
  rfl
theorem s4454 (pattern : Twelve) : d1197 (change pattern 11 10) = d2958 pattern := by
  change (if pattern.h then d1188 (change pattern 11 10) else d674 (change pattern 11 10)) = d2958 pattern
  rw [s4453, s4372]
  rfl
theorem s4455 (pattern : Twelve) : d1212 (change pattern 11 10) = d2959 pattern := by
  change (if pattern.f then d1197 (change pattern 11 10) else d657 (change pattern 11 10)) = d2959 pattern
  rw [s4454, s4283]
  rfl
theorem s4456 (pattern : Twelve) : d1213 (change pattern 11 10) = d2960 pattern := by
  change (if pattern.f then d1196 (change pattern 11 10) else d704 (change pattern 11 10)) = d2960 pattern
  rw [s4447, s4361]
  rfl
theorem s4457 (pattern : Twelve) : d1226 (change pattern 11 10) = d2961 pattern := by
  change (if pattern.e then d1213 (change pattern 11 10) else d1212 (change pattern 11 10)) = d2961 pattern
  rw [s4456, s4455]
  rfl
theorem s4458 (pattern : Twelve) : d1214 (change pattern 11 10) = d2962 pattern := by
  change (if pattern.f then d708 (change pattern 11 10) else d697 (change pattern 11 10)) = d2962 pattern
  rw [s4394, s4327]
  rfl
theorem s4459 (pattern : Twelve) : d1198 (change pattern 11 10) = d2963 pattern := by
  change (if pattern.h then d6 (change pattern 11 10) else d670 (change pattern 11 10)) = d2963 pattern
  rw [s4259, s4330]
  rfl
theorem s4460 (pattern : Twelve) : d1215 (change pattern 11 10) = d2964 pattern := by
  change (if pattern.f then d1198 (change pattern 11 10) else d707 (change pattern 11 10)) = d2964 pattern
  rw [s4459, s4390]
  rfl
theorem s4461 (pattern : Twelve) : d1227 (change pattern 11 10) = d2965 pattern := by
  change (if pattern.e then d1215 (change pattern 11 10) else d1214 (change pattern 11 10)) = d2965 pattern
  rw [s4460, s4458]
  rfl
theorem s4462 (pattern : Twelve) : d1235 (change pattern 11 10) = d2966 pattern := by
  change (if pattern.j then d1227 (change pattern 11 10) else d1226 (change pattern 11 10)) = d2966 pattern
  rw [s4461, s4457]
  rfl
theorem s4463 (pattern : Twelve) : d1236 (change pattern 11 10) = d2967 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d1225 (change pattern 11 10)) = d2967 pattern
  rw [s4259, s4451]
  rfl
theorem s4464 (pattern : Twelve) : d1240 (change pattern 11 10) = d2968 pattern := by
  change (if pattern.d then d1236 (change pattern 11 10) else d1235 (change pattern 11 10)) = d2968 pattern
  rw [s4463, s4462]
  rfl
theorem s4465 (pattern : Twelve) : d1243 (change pattern 11 10) = d2969 pattern := by
  change (if pattern.c then d1240 (change pattern 11 10) else d1234 (change pattern 11 10)) = d2969 pattern
  rw [s4464, s4452]
  rfl
theorem s4466 (pattern : Twelve) : d1246 (change pattern 11 10) = d2970 pattern := by
  change (if pattern.a then d1243 (change pattern 11 10) else d1245 (change pattern 11 10)) = d2970 pattern
  rw [s4465, s4445]
  rfl
theorem s4467 (pattern : Twelve) : d1564 (change pattern 11 10) = d1 pattern := by
  change (if pattern.h then d157 (change pattern 11 10) else d1183 (change pattern 11 10)) = d1 pattern
  rw [s4245, s4402]
  simp only [ite_self]
theorem s4468 (pattern : Twelve) : d1576 (change pattern 11 10) = d1859 pattern := by
  change (if pattern.f then d1564 (change pattern 11 10) else d1190 (change pattern 11 10)) = d1859 pattern
  rw [s4467, s4405]
  rfl
theorem s4469 (pattern : Twelve) : d1577 (change pattern 11 10) = d2971 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d636 (change pattern 11 10)) = d2971 pattern
  rw [s4259, s4258]
  rfl
theorem s4470 (pattern : Twelve) : d1591 (change pattern 11 10) = d2972 pattern := by
  change (if pattern.e then d1577 (change pattern 11 10) else d1576 (change pattern 11 10)) = d2972 pattern
  rw [s4469, s4468]
  rfl
theorem s4471 (pattern : Twelve) : d1557 (change pattern 11 10) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 11 10) else d157 (change pattern 11 10)) = d45 pattern
  rw [s4259, s4245]
  rfl
theorem s4472 (pattern : Twelve) : d1565 (change pattern 11 10) = d2973 pattern := by
  change (if pattern.h then d1557 (change pattern 11 10) else d1184 (change pattern 11 10)) = d2973 pattern
  rw [s4471, s4406]
  rfl
theorem s4473 (pattern : Twelve) : d1578 (change pattern 11 10) = d2974 pattern := by
  change (if pattern.f then d1565 (change pattern 11 10) else d692 (change pattern 11 10)) = d2974 pattern
  rw [s4472, s4303]
  rfl
theorem s4474 (pattern : Twelve) : d1566 (change pattern 11 10) = d2973 pattern := by
  change (if pattern.h then d651 (change pattern 11 10) else d1184 (change pattern 11 10)) = d2973 pattern
  rw [s4260, s4406]
  rfl
theorem s4475 (pattern : Twelve) : d1579 (change pattern 11 10) = d2975 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1566 (change pattern 11 10)) = d2975 pattern
  rw [s4259, s4474]
  rfl
theorem s4476 (pattern : Twelve) : d1592 (change pattern 11 10) = d2976 pattern := by
  change (if pattern.e then d1579 (change pattern 11 10) else d1578 (change pattern 11 10)) = d2976 pattern
  rw [s4475, s4473]
  rfl
theorem s4477 (pattern : Twelve) : d1600 (change pattern 11 10) = d2977 pattern := by
  change (if pattern.j then d1592 (change pattern 11 10) else d1591 (change pattern 11 10)) = d2977 pattern
  rw [s4476, s4470]
  rfl
theorem s4478 (pattern : Twelve) : d1580 (change pattern 11 10) = d1859 pattern := by
  change (if pattern.f then d1564 (change pattern 11 10) else d158 (change pattern 11 10)) = d1859 pattern
  rw [s4467, s4240]
  rfl
theorem s4479 (pattern : Twelve) : d1593 (change pattern 11 10) = d2972 pattern := by
  change (if pattern.e then d1577 (change pattern 11 10) else d1580 (change pattern 11 10)) = d2972 pattern
  rw [s4469, s4478]
  rfl
theorem s4480 (pattern : Twelve) : d1601 (change pattern 11 10) = d2977 pattern := by
  change (if pattern.j then d1592 (change pattern 11 10) else d1593 (change pattern 11 10)) = d2977 pattern
  rw [s4476, s4479]
  rfl
theorem s4481 (pattern : Twelve) : d1607 (change pattern 11 10) = d2977 pattern := by
  change (if pattern.d then d1601 (change pattern 11 10) else d1600 (change pattern 11 10)) = d2977 pattern
  rw [s4480, s4477]
  simp only [ite_self]
theorem s4482 (pattern : Twelve) : d1558 (change pattern 11 10) = d46 pattern := by
  change (if pattern.i then d159 (change pattern 11 10) else d157 (change pattern 11 10)) = d46 pattern
  rw [s4315, s4245]
  rfl
theorem s4483 (pattern : Twelve) : d1567 (change pattern 11 10) = d46 pattern := by
  change (if pattern.h then d1558 (change pattern 11 10) else d1184 (change pattern 11 10)) = d46 pattern
  rw [s4482, s4406]
  simp only [ite_self]
theorem s4484 (pattern : Twelve) : d1581 (change pattern 11 10) = d2978 pattern := by
  change (if pattern.f then d1567 (change pattern 11 10) else d657 (change pattern 11 10)) = d2978 pattern
  rw [s4483, s4283]
  rfl
theorem s4485 (pattern : Twelve) : d1582 (change pattern 11 10) = d2979 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1184 (change pattern 11 10)) = d2979 pattern
  rw [s4259, s4406]
  rfl
theorem s4486 (pattern : Twelve) : d1594 (change pattern 11 10) = d2980 pattern := by
  change (if pattern.e then d1582 (change pattern 11 10) else d1581 (change pattern 11 10)) = d2980 pattern
  rw [s4485, s4484]
  rfl
theorem s4487 (pattern : Twelve) : d1568 (change pattern 11 10) = d2981 pattern := by
  change (if pattern.h then d677 (change pattern 11 10) else d1186 (change pattern 11 10)) = d2981 pattern
  rw [s4389, s4427]
  rfl
theorem s4488 (pattern : Twelve) : d1583 (change pattern 11 10) = d2982 pattern := by
  change (if pattern.f then d1568 (change pattern 11 10) else d697 (change pattern 11 10)) = d2982 pattern
  rw [s4487, s4327]
  rfl
theorem s4489 (pattern : Twelve) : d1569 (change pattern 11 10) = d2981 pattern := by
  change (if pattern.h then d670 (change pattern 11 10) else d1186 (change pattern 11 10)) = d2981 pattern
  rw [s4330, s4427]
  rfl
theorem s4490 (pattern : Twelve) : d1584 (change pattern 11 10) = d2983 pattern := by
  change (if pattern.f then d6 (change pattern 11 10) else d1569 (change pattern 11 10)) = d2983 pattern
  rw [s4259, s4489]
  rfl
theorem s4491 (pattern : Twelve) : d1595 (change pattern 11 10) = d2984 pattern := by
  change (if pattern.e then d1584 (change pattern 11 10) else d1583 (change pattern 11 10)) = d2984 pattern
  rw [s4490, s4488]
  rfl
theorem s4492 (pattern : Twelve) : d1602 (change pattern 11 10) = d2985 pattern := by
  change (if pattern.j then d1595 (change pattern 11 10) else d1594 (change pattern 11 10)) = d2985 pattern
  rw [s4491, s4486]
  rfl
theorem s4493 (pattern : Twelve) : d1603 (change pattern 11 10) = d2986 pattern := by
  change (if pattern.j then d6 (change pattern 11 10) else d1592 (change pattern 11 10)) = d2986 pattern
  rw [s4259, s4476]
  rfl
theorem s4494 (pattern : Twelve) : d1608 (change pattern 11 10) = d2987 pattern := by
  change (if pattern.d then d1603 (change pattern 11 10) else d1602 (change pattern 11 10)) = d2987 pattern
  rw [s4493, s4492]
  rfl
theorem s4495 (pattern : Twelve) : d1610 (change pattern 11 10) = d2988 pattern := by
  change (if pattern.c then d1608 (change pattern 11 10) else d1607 (change pattern 11 10)) = d2988 pattern
  rw [s4494, s4481]
  rfl
theorem s4496 (pattern : Twelve) : d1611 (change pattern 11 10) = d2988 pattern := by
  change (if pattern.c then d1608 (change pattern 11 10) else d1601 (change pattern 11 10)) = d2988 pattern
  rw [s4494, s4480]
  rfl
theorem s4497 (pattern : Twelve) : d1613 (change pattern 11 10) = d2988 pattern := by
  change (if pattern.g then d1611 (change pattern 11 10) else d1610 (change pattern 11 10)) = d2988 pattern
  rw [s4496, s4495]
  simp only [ite_self]
theorem s4498 (pattern : Twelve) : d1614 (change pattern 11 10) = d2988 pattern := by
  change (if pattern.b then d1611 (change pattern 11 10) else d1613 (change pattern 11 10)) = d2988 pattern
  rw [s4496, s4497]
  simp only [ite_self]
theorem s4499 (pattern : Twelve) : d1559 (change pattern 11 10) = d2989 pattern := by
  change (if pattern.i then d635 (change pattern 11 10) else d636 (change pattern 11 10)) = d2989 pattern
  rw [s4256, s4258]
  rfl
end NetHack.Sokoban21.Diagram
