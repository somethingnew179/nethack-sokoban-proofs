/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions30
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3720 (p : Pattern) : d1158 (change p 163 none) = d42 p := by
  change d42 (change p 163 none) = d42 p
  exact sub3719 p
theorem sub3721 (p : Pattern) : d1159 (change p 163 none) = d4307 p := by
  change (if p 162 then d1158 (change p 163 none) else d1157 (change p 163 none)) = d4307 p
  rw [sub3720, sub3714]
  rfl
theorem sub3722 (p : Pattern) : d46 (change p 163 none) = d46 p := by
  change (if p 182 then d12 (change p 163 none) else d14 (change p 163 none)) = d46 p
  rw [sub3692, sub3694]
  rfl
theorem sub3723 (p : Pattern) : d1160 (change p 163 none) = d46 p := by
  change d46 (change p 163 none) = d46 p
  exact sub3722 p
theorem sub3724 (p : Pattern) : d48 (change p 163 none) = d48 p := by
  change (if p 182 then d12 (change p 163 none) else d24 (change p 163 none)) = d48 p
  rw [sub3692, sub3703]
  rfl
theorem sub3725 (p : Pattern) : d49 (change p 163 none) = d48 p := by
  change d48 (change p 163 none) = d48 p
  exact sub3724 p
theorem sub3726 (p : Pattern) : d1161 (change p 163 none) = d4308 p := by
  change (if p 162 then d49 (change p 163 none) else d1160 (change p 163 none)) = d4308 p
  rw [sub3725, sub3723]
  rfl
theorem sub3727 (p : Pattern) : d1162 (change p 163 none) = d4309 p := by
  change (if p 161 then d1161 (change p 163 none) else d1159 (change p 163 none)) = d4309 p
  rw [sub3726, sub3721]
  rfl
theorem sub3728 (p : Pattern) : d1163 (change p 163 none) = d4310 p := by
  change (if p 160 then d1162 (change p 163 none) else d1156 (change p 163 none)) = d4310 p
  rw [sub3727, sub3708]
  rfl
theorem sub3729 (p : Pattern) : d1164 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3730 (p : Pattern) : d53 (change p 163 none) = d53 p := by
  change (if p 182 then d32 (change p 163 none) else d31 (change p 163 none)) = d53 p
  rw [sub3712, sub3711]
  rfl
theorem sub3731 (p : Pattern) : d1165 (change p 163 none) = d53 p := by
  change d53 (change p 163 none) = d53 p
  exact sub3730 p
theorem sub3732 (p : Pattern) : d1166 (change p 163 none) = d4311 p := by
  change (if p 162 then d1165 (change p 163 none) else d1164 (change p 163 none)) = d4311 p
  rw [sub3731, sub3729]
  rfl
theorem sub3733 (p : Pattern) : d1167 (change p 163 none) = d53 p := by
  change d53 (change p 163 none) = d53 p
  exact sub3730 p
theorem sub3734 (p : Pattern) : d62 (change p 163 none) = d62 p := by
  change (if p 182 then d41 (change p 163 none) else d40 (change p 163 none)) = d62 p
  rw [sub3718, sub3717]
  rfl
theorem sub3735 (p : Pattern) : d63 (change p 163 none) = d62 p := by
  change d62 (change p 163 none) = d62 p
  exact sub3734 p
theorem sub3736 (p : Pattern) : d1168 (change p 163 none) = d4312 p := by
  change (if p 162 then d63 (change p 163 none) else d1167 (change p 163 none)) = d4312 p
  rw [sub3735, sub3733]
  rfl
theorem sub3737 (p : Pattern) : d1169 (change p 163 none) = d4313 p := by
  change (if p 161 then d1168 (change p 163 none) else d1166 (change p 163 none)) = d4313 p
  rw [sub3736, sub3732]
  rfl
theorem sub3738 (p : Pattern) : d1170 (change p 163 none) = d53 p := by
  change d53 (change p 163 none) = d53 p
  exact sub3730 p
theorem sub3739 (p : Pattern) : d66 (change p 163 none) = d66 p := by
  change (if p 182 then d12 (change p 163 none) else d31 (change p 163 none)) = d66 p
  rw [sub3692, sub3711]
  rfl
theorem sub3740 (p : Pattern) : d1171 (change p 163 none) = d66 p := by
  change d66 (change p 163 none) = d66 p
  exact sub3739 p
theorem sub3741 (p : Pattern) : d1172 (change p 163 none) = d4314 p := by
  change (if p 162 then d1171 (change p 163 none) else d1170 (change p 163 none)) = d4314 p
  rw [sub3740, sub3738]
  rfl
theorem sub3742 (p : Pattern) : d72 (change p 163 none) = d72 p := by
  change (if p 182 then d12 (change p 163 none) else d40 (change p 163 none)) = d72 p
  rw [sub3692, sub3717]
  rfl
theorem sub3743 (p : Pattern) : d73 (change p 163 none) = d72 p := by
  change d72 (change p 163 none) = d72 p
  exact sub3742 p
theorem sub3744 (p : Pattern) : d1173 (change p 163 none) = d4315 p := by
  change (if p 162 then d73 (change p 163 none) else d1171 (change p 163 none)) = d4315 p
  rw [sub3743, sub3740]
  rfl
theorem sub3745 (p : Pattern) : d1174 (change p 163 none) = d4316 p := by
  change (if p 161 then d1173 (change p 163 none) else d1172 (change p 163 none)) = d4316 p
  rw [sub3744, sub3741]
  rfl
theorem sub3746 (p : Pattern) : d1175 (change p 163 none) = d4317 p := by
  change (if p 160 then d1174 (change p 163 none) else d1169 (change p 163 none)) = d4317 p
  rw [sub3745, sub3737]
  rfl
theorem sub3747 (p : Pattern) : d1176 (change p 163 none) = d4318 p := by
  change (if p 141 then d1175 (change p 163 none) else d1163 (change p 163 none)) = d4318 p
  rw [sub3746, sub3728]
  rfl
theorem sub3748 (p : Pattern) : d1177 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3749 (p : Pattern) : d1178 (change p 163 none) = d16 p := by
  change (if p 162 then d1177 (change p 163 none) else d1154 (change p 163 none)) = d16 p
  rw [sub3748, sub3700]
  simp only [ite_self]
theorem sub3750 (p : Pattern) : d1179 (change p 163 none) = d4305 p := by
  change (if p 162 then d27 (change p 163 none) else d1177 (change p 163 none)) = d4305 p
  rw [sub3706, sub3748]
  rfl
theorem sub3751 (p : Pattern) : d1180 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1178 (change p 163 none)) = d4306 p
  rw [sub3750, sub3749]
  rfl
theorem sub3752 (p : Pattern) : d1181 (change p 163 none) = d53 p := by
  change d53 (change p 163 none) = d53 p
  exact sub3730 p
theorem sub3753 (p : Pattern) : d1182 (change p 163 none) = d4312 p := by
  change (if p 162 then d63 (change p 163 none) else d1181 (change p 163 none)) = d4312 p
  rw [sub3735, sub3752]
  rfl
theorem sub3754 (p : Pattern) : d1183 (change p 163 none) = d4319 p := by
  change (if p 161 then d12 (change p 163 none) else d1182 (change p 163 none)) = d4319 p
  rw [sub3692, sub3753]
  rfl
theorem sub3755 (p : Pattern) : d1184 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1180 (change p 163 none)) = d4320 p
  rw [sub3754, sub3751]
  rfl
theorem sub3756 (p : Pattern) : d1185 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3757 (p : Pattern) : d1186 (change p 163 none) = d4311 p := by
  change (if p 162 then d1181 (change p 163 none) else d1185 (change p 163 none)) = d4311 p
  rw [sub3752, sub3756]
  rfl
theorem sub3758 (p : Pattern) : d1187 (change p 163 none) = d4313 p := by
  change (if p 161 then d1182 (change p 163 none) else d1186 (change p 163 none)) = d4313 p
  rw [sub3753, sub3757]
  rfl
theorem sub3759 (p : Pattern) : d1188 (change p 163 none) = d968 p := by
  change (if p 162 then d12 (change p 163 none) else d1181 (change p 163 none)) = d968 p
  rw [sub3692, sub3752]
  rfl
theorem sub3760 (p : Pattern) : d1189 (change p 163 none) = d969 p := by
  change (if p 161 then d12 (change p 163 none) else d1188 (change p 163 none)) = d969 p
  rw [sub3692, sub3759]
  rfl
theorem sub3761 (p : Pattern) : d1190 (change p 163 none) = d4321 p := by
  change (if p 160 then d1189 (change p 163 none) else d1187 (change p 163 none)) = d4321 p
  rw [sub3760, sub3758]
  rfl
theorem sub3762 (p : Pattern) : d1191 (change p 163 none) = d4322 p := by
  change (if p 141 then d1190 (change p 163 none) else d1184 (change p 163 none)) = d4322 p
  rw [sub3761, sub3755]
  rfl
theorem sub3763 (p : Pattern) : d1192 (change p 163 none) = d4323 p := by
  change (if p 138 then d1191 (change p 163 none) else d1176 (change p 163 none)) = d4323 p
  rw [sub3762, sub3747]
  rfl
theorem sub3764 (p : Pattern) : d1193 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3765 (p : Pattern) : d1194 (change p 163 none) = d16 p := by
  change (if p 162 then d1193 (change p 163 none) else d1152 (change p 163 none)) = d16 p
  rw [sub3764, sub3698]
  simp only [ite_self]
theorem sub3766 (p : Pattern) : d1195 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1194 (change p 163 none)) = d4306 p
  rw [sub3750, sub3765]
  rfl
theorem sub3767 (p : Pattern) : d1196 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1195 (change p 163 none)) = d4320 p
  rw [sub3754, sub3766]
  rfl
theorem sub3768 (p : Pattern) : d1197 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3769 (p : Pattern) : d1198 (change p 163 none) = d4311 p := by
  change (if p 162 then d1181 (change p 163 none) else d1197 (change p 163 none)) = d4311 p
  rw [sub3752, sub3768]
  rfl
theorem sub3770 (p : Pattern) : d1199 (change p 163 none) = d4313 p := by
  change (if p 161 then d1182 (change p 163 none) else d1198 (change p 163 none)) = d4313 p
  rw [sub3753, sub3769]
  rfl
theorem sub3771 (p : Pattern) : d1200 (change p 163 none) = d4321 p := by
  change (if p 160 then d1189 (change p 163 none) else d1199 (change p 163 none)) = d4321 p
  rw [sub3760, sub3770]
  rfl
theorem sub3772 (p : Pattern) : d1201 (change p 163 none) = d4322 p := by
  change (if p 141 then d1200 (change p 163 none) else d1196 (change p 163 none)) = d4322 p
  rw [sub3771, sub3767]
  rfl
theorem sub3773 (p : Pattern) : d1202 (change p 163 none) = d4324 p := by
  change (if p 162 then d63 (change p 163 none) else d27 (change p 163 none)) = d4324 p
  rw [sub3735, sub3706]
  rfl
theorem sub3774 (p : Pattern) : d91 (change p 163 none) = d4160 p := by
  change (if p 162 then d12 (change p 163 none) else d63 (change p 163 none)) = d4160 p
  rw [sub3692, sub3735]
  rfl
theorem sub3775 (p : Pattern) : d1203 (change p 163 none) = d4325 p := by
  change (if p 161 then d91 (change p 163 none) else d1202 (change p 163 none)) = d4325 p
  rw [sub3774, sub3773]
  rfl
theorem sub3776 (p : Pattern) : d93 (change p 163 none) = d4161 p := by
  change (if p 161 then d12 (change p 163 none) else d91 (change p 163 none)) = d4161 p
  rw [sub3692, sub3774]
  rfl
theorem sub3777 (p : Pattern) : d1204 (change p 163 none) = d4326 p := by
  change (if p 160 then d93 (change p 163 none) else d1203 (change p 163 none)) = d4326 p
  rw [sub3776, sub3775]
  rfl
theorem sub3778 (p : Pattern) : d95 (change p 163 none) = d4162 p := by
  change (if p 160 then d12 (change p 163 none) else d93 (change p 163 none)) = d4162 p
  rw [sub3692, sub3776]
  rfl
theorem sub3779 (p : Pattern) : d1205 (change p 163 none) = d4327 p := by
  change (if p 141 then d95 (change p 163 none) else d1204 (change p 163 none)) = d4327 p
  rw [sub3778, sub3777]
  rfl
theorem sub3780 (p : Pattern) : d1206 (change p 163 none) = d4328 p := by
  change (if p 138 then d1205 (change p 163 none) else d1201 (change p 163 none)) = d4328 p
  rw [sub3779, sub3772]
  rfl
theorem sub3781 (p : Pattern) : d1207 (change p 163 none) = d4329 p := by
  change (if p 116 then d1206 (change p 163 none) else d1192 (change p 163 none)) = d4329 p
  rw [sub3780, sub3763]
  rfl
theorem sub3782 (p : Pattern) : d1208 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3783 (p : Pattern) : d1209 (change p 163 none) = d16 p := by
  change (if p 162 then d1185 (change p 163 none) else d1208 (change p 163 none)) = d16 p
  rw [sub3756, sub3782]
  simp only [ite_self]
theorem sub3784 (p : Pattern) : d1210 (change p 163 none) = d4305 p := by
  change (if p 162 then d27 (change p 163 none) else d1193 (change p 163 none)) = d4305 p
  rw [sub3706, sub3764]
  rfl
theorem sub3785 (p : Pattern) : d1211 (change p 163 none) = d4306 p := by
  change (if p 161 then d1210 (change p 163 none) else d1209 (change p 163 none)) = d4306 p
  rw [sub3784, sub3783]
  rfl
theorem sub3786 (p : Pattern) : d1212 (change p 163 none) = d33 p := by
  change d33 (change p 163 none) = d33 p
  exact sub3713 p
theorem sub3787 (p : Pattern) : d1213 (change p 163 none) = d4307 p := by
  change (if p 162 then d1158 (change p 163 none) else d1212 (change p 163 none)) = d4307 p
  rw [sub3720, sub3786]
  rfl
theorem sub3788 (p : Pattern) : d1214 (change p 163 none) = d4309 p := by
  change (if p 161 then d1161 (change p 163 none) else d1213 (change p 163 none)) = d4309 p
  rw [sub3726, sub3787]
  rfl
theorem sub3789 (p : Pattern) : d1215 (change p 163 none) = d4310 p := by
  change (if p 160 then d1214 (change p 163 none) else d1211 (change p 163 none)) = d4310 p
  rw [sub3788, sub3785]
  rfl
theorem sub3790 (p : Pattern) : d1216 (change p 163 none) = d4311 p := by
  change (if p 162 then d1181 (change p 163 none) else d1154 (change p 163 none)) = d4311 p
  rw [sub3752, sub3700]
  rfl
theorem sub3791 (p : Pattern) : d1217 (change p 163 none) = d4313 p := by
  change (if p 161 then d1182 (change p 163 none) else d1216 (change p 163 none)) = d4313 p
  rw [sub3753, sub3790]
  rfl
theorem sub3792 (p : Pattern) : d1218 (change p 163 none) = d4314 p := by
  change (if p 162 then d1171 (change p 163 none) else d1181 (change p 163 none)) = d4314 p
  rw [sub3740, sub3752]
  rfl
theorem sub3793 (p : Pattern) : d1219 (change p 163 none) = d4316 p := by
  change (if p 161 then d1173 (change p 163 none) else d1218 (change p 163 none)) = d4316 p
  rw [sub3744, sub3792]
  rfl
theorem sub3794 (p : Pattern) : d1220 (change p 163 none) = d4317 p := by
  change (if p 160 then d1219 (change p 163 none) else d1217 (change p 163 none)) = d4317 p
  rw [sub3793, sub3791]
  rfl
theorem sub3795 (p : Pattern) : d1221 (change p 163 none) = d4318 p := by
  change (if p 141 then d1220 (change p 163 none) else d1215 (change p 163 none)) = d4318 p
  rw [sub3794, sub3789]
  rfl
theorem sub3796 (p : Pattern) : d1222 (change p 163 none) = d16 p := by
  change (if p 162 then d1177 (change p 163 none) else d1193 (change p 163 none)) = d16 p
  rw [sub3748, sub3764]
  simp only [ite_self]
theorem sub3797 (p : Pattern) : d1223 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1222 (change p 163 none)) = d4306 p
  rw [sub3750, sub3796]
  rfl
theorem sub3798 (p : Pattern) : d1224 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1223 (change p 163 none)) = d4320 p
  rw [sub3754, sub3797]
  rfl
theorem sub3799 (p : Pattern) : d1225 (change p 163 none) = d4311 p := by
  change (if p 162 then d1181 (change p 163 none) else d1177 (change p 163 none)) = d4311 p
  rw [sub3752, sub3748]
  rfl
theorem sub3800 (p : Pattern) : d1226 (change p 163 none) = d4313 p := by
  change (if p 161 then d1182 (change p 163 none) else d1225 (change p 163 none)) = d4313 p
  rw [sub3753, sub3799]
  rfl
theorem sub3801 (p : Pattern) : d1227 (change p 163 none) = d4321 p := by
  change (if p 160 then d1189 (change p 163 none) else d1226 (change p 163 none)) = d4321 p
  rw [sub3760, sub3800]
  rfl
theorem sub3802 (p : Pattern) : d1228 (change p 163 none) = d4322 p := by
  change (if p 141 then d1227 (change p 163 none) else d1224 (change p 163 none)) = d4322 p
  rw [sub3801, sub3798]
  rfl
theorem sub3803 (p : Pattern) : d1229 (change p 163 none) = d4323 p := by
  change (if p 138 then d1228 (change p 163 none) else d1221 (change p 163 none)) = d4323 p
  rw [sub3802, sub3795]
  rfl
theorem sub3804 (p : Pattern) : d1230 (change p 163 none) = d16 p := by
  change (if p 162 then d1177 (change p 163 none) else d1185 (change p 163 none)) = d16 p
  rw [sub3748, sub3756]
  simp only [ite_self]
theorem sub3805 (p : Pattern) : d1231 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1230 (change p 163 none)) = d4306 p
  rw [sub3750, sub3804]
  rfl
theorem sub3806 (p : Pattern) : d1232 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1231 (change p 163 none)) = d4320 p
  rw [sub3754, sub3805]
  rfl
theorem sub3807 (p : Pattern) : d1233 (change p 163 none) = d4322 p := by
  change (if p 141 then d1227 (change p 163 none) else d1232 (change p 163 none)) = d4322 p
  rw [sub3801, sub3806]
  rfl
theorem sub3808 (p : Pattern) : d1234 (change p 163 none) = d4330 p := by
  change (if p 138 then d12 (change p 163 none) else d1233 (change p 163 none)) = d4330 p
  rw [sub3692, sub3807]
  rfl
theorem sub3809 (p : Pattern) : d1235 (change p 163 none) = d4331 p := by
  change (if p 116 then d1234 (change p 163 none) else d1229 (change p 163 none)) = d4331 p
  rw [sub3808, sub3803]
  rfl
theorem sub3810 (p : Pattern) : d1236 (change p 163 none) = d4332 p := by
  change (if p 115 then d1235 (change p 163 none) else d1207 (change p 163 none)) = d4332 p
  rw [sub3809, sub3781]
  rfl
theorem sub3811 (p : Pattern) : d1237 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3812 (p : Pattern) : d1238 (change p 163 none) = d16 p := by
  change (if p 162 then d1154 (change p 163 none) else d1237 (change p 163 none)) = d16 p
  rw [sub3700, sub3811]
  simp only [ite_self]
theorem sub3813 (p : Pattern) : d1239 (change p 163 none) = d4305 p := by
  change (if p 162 then d27 (change p 163 none) else d1197 (change p 163 none)) = d4305 p
  rw [sub3706, sub3768]
  rfl
theorem sub3814 (p : Pattern) : d1240 (change p 163 none) = d4306 p := by
  change (if p 161 then d1239 (change p 163 none) else d1238 (change p 163 none)) = d4306 p
  rw [sub3813, sub3812]
  rfl
theorem sub3815 (p : Pattern) : d1241 (change p 163 none) = d33 p := by
  change d33 (change p 163 none) = d33 p
  exact sub3713 p
theorem sub3816 (p : Pattern) : d1242 (change p 163 none) = d4307 p := by
  change (if p 162 then d1158 (change p 163 none) else d1241 (change p 163 none)) = d4307 p
  rw [sub3720, sub3815]
  rfl
theorem sub3817 (p : Pattern) : d1243 (change p 163 none) = d4309 p := by
  change (if p 161 then d1161 (change p 163 none) else d1242 (change p 163 none)) = d4309 p
  rw [sub3726, sub3816]
  rfl
theorem sub3818 (p : Pattern) : d1244 (change p 163 none) = d4310 p := by
  change (if p 160 then d1243 (change p 163 none) else d1240 (change p 163 none)) = d4310 p
  rw [sub3817, sub3814]
  rfl
theorem sub3819 (p : Pattern) : d1245 (change p 163 none) = d4311 p := by
  change (if p 162 then d1167 (change p 163 none) else d1208 (change p 163 none)) = d4311 p
  rw [sub3733, sub3782]
  rfl
theorem sub3820 (p : Pattern) : d1246 (change p 163 none) = d4312 p := by
  change (if p 162 then d63 (change p 163 none) else d1170 (change p 163 none)) = d4312 p
  rw [sub3735, sub3738]
  rfl
theorem sub3821 (p : Pattern) : d1247 (change p 163 none) = d4313 p := by
  change (if p 161 then d1246 (change p 163 none) else d1245 (change p 163 none)) = d4313 p
  rw [sub3820, sub3819]
  rfl
theorem sub3822 (p : Pattern) : d1248 (change p 163 none) = d4317 p := by
  change (if p 160 then d1219 (change p 163 none) else d1247 (change p 163 none)) = d4317 p
  rw [sub3793, sub3821]
  rfl
theorem sub3823 (p : Pattern) : d1249 (change p 163 none) = d4318 p := by
  change (if p 141 then d1248 (change p 163 none) else d1244 (change p 163 none)) = d4318 p
  rw [sub3822, sub3818]
  rfl
theorem sub3824 (p : Pattern) : d1250 (change p 163 none) = d16 p := by
  change (if p 162 then d1177 (change p 163 none) else d1197 (change p 163 none)) = d16 p
  rw [sub3748, sub3768]
  simp only [ite_self]
theorem sub3825 (p : Pattern) : d1251 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1250 (change p 163 none)) = d4306 p
  rw [sub3750, sub3824]
  rfl
theorem sub3826 (p : Pattern) : d1252 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1251 (change p 163 none)) = d4320 p
  rw [sub3754, sub3825]
  rfl
theorem sub3827 (p : Pattern) : d1253 (change p 163 none) = d4311 p := by
  change (if p 162 then d1181 (change p 163 none) else d1193 (change p 163 none)) = d4311 p
  rw [sub3752, sub3764]
  rfl
theorem sub3828 (p : Pattern) : d1254 (change p 163 none) = d4313 p := by
  change (if p 161 then d1182 (change p 163 none) else d1253 (change p 163 none)) = d4313 p
  rw [sub3753, sub3827]
  rfl
theorem sub3829 (p : Pattern) : d1255 (change p 163 none) = d4321 p := by
  change (if p 160 then d1189 (change p 163 none) else d1254 (change p 163 none)) = d4321 p
  rw [sub3760, sub3828]
  rfl
theorem sub3830 (p : Pattern) : d1256 (change p 163 none) = d4322 p := by
  change (if p 141 then d1255 (change p 163 none) else d1252 (change p 163 none)) = d4322 p
  rw [sub3829, sub3826]
  rfl
theorem sub3831 (p : Pattern) : d1257 (change p 163 none) = d4323 p := by
  change (if p 138 then d1256 (change p 163 none) else d1249 (change p 163 none)) = d4323 p
  rw [sub3830, sub3823]
  rfl
theorem sub3832 (p : Pattern) : d1258 (change p 163 none) = d4328 p := by
  change (if p 138 then d1205 (change p 163 none) else d1191 (change p 163 none)) = d4328 p
  rw [sub3779, sub3762]
  rfl
theorem sub3833 (p : Pattern) : d1259 (change p 163 none) = d4329 p := by
  change (if p 116 then d1258 (change p 163 none) else d1257 (change p 163 none)) = d4329 p
  rw [sub3832, sub3831]
  rfl
theorem sub3834 (p : Pattern) : d1260 (change p 163 none) = d4310 p := by
  change (if p 160 then d1214 (change p 163 none) else d1195 (change p 163 none)) = d4310 p
  rw [sub3788, sub3766]
  rfl
theorem sub3835 (p : Pattern) : d1261 (change p 163 none) = d4317 p := by
  change (if p 160 then d1219 (change p 163 none) else d1199 (change p 163 none)) = d4317 p
  rw [sub3793, sub3770]
  rfl
theorem sub3836 (p : Pattern) : d1262 (change p 163 none) = d4318 p := by
  change (if p 141 then d1261 (change p 163 none) else d1260 (change p 163 none)) = d4318 p
  rw [sub3835, sub3834]
  rfl
theorem sub3837 (p : Pattern) : d1263 (change p 163 none) = d4306 p := by
  change (if p 161 then d1179 (change p 163 none) else d1177 (change p 163 none)) = d4306 p
  rw [sub3750, sub3748]
  rfl
theorem sub3838 (p : Pattern) : d1264 (change p 163 none) = d4320 p := by
  change (if p 160 then d1183 (change p 163 none) else d1263 (change p 163 none)) = d4320 p
  rw [sub3754, sub3837]
  rfl
theorem sub3839 (p : Pattern) : d1265 (change p 163 none) = d4322 p := by
  change (if p 141 then d1227 (change p 163 none) else d1264 (change p 163 none)) = d4322 p
  rw [sub3801, sub3838]
  rfl
end NetHack.Sokoban22Refined85
