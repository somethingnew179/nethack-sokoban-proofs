/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions33
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4080 (p : Pattern) : d86 (change p 10000 (some 160)) = d85 p := by
  change d85 (change p 10000 (some 160)) = d85 p
  exact sub4079 p
theorem sub4081 (p : Pattern) : d87 (change p 10000 (some 160)) = d4399 p := by
  change (if p 141 then d86 (change p 10000 (some 160)) else d82 (change p 10000 (some 160))) = d4399 p
  rw [sub4080, sub4076]
  rfl
theorem sub4082 (p : Pattern) : d88 (change p 10000 (some 160)) = d4400 p := by
  change (if p 138 then d87 (change p 10000 (some 160)) else d77 (change p 10000 (some 160))) = d4400 p
  rw [sub4081, sub4068]
  rfl
theorem sub4083 (p : Pattern) : d91 (change p 10000 (some 160)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d63 (change p 10000 (some 160))) = d91 p
  rw [sub4019, sub4073]
  rfl
theorem sub4084 (p : Pattern) : d93 (change p 10000 (some 160)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d91 (change p 10000 (some 160))) = d93 p
  rw [sub4019, sub4083]
  rfl
theorem sub4085 (p : Pattern) : d94 (change p 10000 (some 160)) = d93 p := by
  change d93 (change p 10000 (some 160)) = d93 p
  exact sub4084 p
theorem sub4086 (p : Pattern) : d95 (change p 10000 (some 160)) = d12 p := by
  change d12 (change p 10000 (some 160)) = d12 p
  exact sub4019 p
theorem sub4087 (p : Pattern) : d96 (change p 10000 (some 160)) = d4401 p := by
  change (if p 141 then d95 (change p 10000 (some 160)) else d94 (change p 10000 (some 160))) = d4401 p
  rw [sub4086, sub4085]
  rfl
theorem sub4088 (p : Pattern) : d97 (change p 10000 (some 160)) = d4402 p := by
  change (if p 138 then d96 (change p 10000 (some 160)) else d87 (change p 10000 (some 160))) = d4402 p
  rw [sub4087, sub4081]
  rfl
theorem sub4089 (p : Pattern) : d98 (change p 10000 (some 160)) = d4403 p := by
  change (if p 116 then d97 (change p 10000 (some 160)) else d88 (change p 10000 (some 160))) = d4403 p
  rw [sub4088, sub4082]
  rfl
theorem sub4090 (p : Pattern) : d99 (change p 10000 (some 160)) = d4404 p := by
  change (if p 138 then d12 (change p 10000 (some 160)) else d87 (change p 10000 (some 160))) = d4404 p
  rw [sub4019, sub4081]
  rfl
theorem sub4091 (p : Pattern) : d100 (change p 10000 (some 160)) = d4405 p := by
  change (if p 116 then d99 (change p 10000 (some 160)) else d88 (change p 10000 (some 160))) = d4405 p
  rw [sub4090, sub4082]
  rfl
theorem sub4092 (p : Pattern) : d101 (change p 10000 (some 160)) = d4406 p := by
  change (if p 115 then d100 (change p 10000 (some 160)) else d98 (change p 10000 (some 160))) = d4406 p
  rw [sub4091, sub4089]
  rfl
theorem sub4093 (p : Pattern) : d1 (change p 10000 (some 160)) = d1 p := by
  rfl
theorem sub4094 (p : Pattern) : d102 (change p 10000 (some 160)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d1 (change p 10000 (some 160))) = d102 p
  rw [sub4019, sub4093]
  rfl
theorem sub4095 (p : Pattern) : d103 (change p 10000 (some 160)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 160)) else d1 (change p 10000 (some 160))) = d103 p
  rw [sub4094, sub4093]
  rfl
theorem sub4096 (p : Pattern) : d3 (change p 10000 (some 160)) = d3 p := by
  rfl
theorem sub4097 (p : Pattern) : d115 (change p 10000 (some 160)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d3 (change p 10000 (some 160))) = d115 p
  rw [sub4019, sub4096]
  rfl
theorem sub4098 (p : Pattern) : d116 (change p 10000 (some 160)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 160)) else d3 (change p 10000 (some 160))) = d116 p
  rw [sub4097, sub4096]
  rfl
theorem sub4099 (p : Pattern) : d117 (change p 10000 (some 160)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d116 (change p 10000 (some 160))) = d117 p
  rw [sub4019, sub4098]
  rfl
theorem sub4100 (p : Pattern) : d118 (change p 10000 (some 160)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 160)) else d103 (change p 10000 (some 160))) = d118 p
  rw [sub4099, sub4095]
  rfl
theorem sub4101 (p : Pattern) : d7 (change p 10000 (some 160)) = d7 p := by
  rfl
theorem sub4102 (p : Pattern) : d119 (change p 10000 (some 160)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d7 (change p 10000 (some 160))) = d119 p
  rw [sub4019, sub4101]
  rfl
theorem sub4103 (p : Pattern) : d120 (change p 10000 (some 160)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 160)) else d7 (change p 10000 (some 160))) = d120 p
  rw [sub4102, sub4101]
  rfl
theorem sub4104 (p : Pattern) : d121 (change p 10000 (some 160)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d120 (change p 10000 (some 160))) = d121 p
  rw [sub4019, sub4103]
  rfl
theorem sub4105 (p : Pattern) : d122 (change p 10000 (some 160)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 160)) else d103 (change p 10000 (some 160))) = d122 p
  rw [sub4104, sub4095]
  rfl
theorem sub4106 (p : Pattern) : d123 (change p 10000 (some 160)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 160)) else d118 (change p 10000 (some 160))) = d123 p
  rw [sub4105, sub4100]
  rfl
theorem sub4107 (p : Pattern) : d124 (change p 10000 (some 160)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d103 (change p 10000 (some 160))) = d124 p
  rw [sub4019, sub4095]
  rfl
theorem sub4108 (p : Pattern) : d5 (change p 10000 (some 160)) = d5 p := by
  rfl
theorem sub4109 (p : Pattern) : d106 (change p 10000 (some 160)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d5 (change p 10000 (some 160))) = d106 p
  rw [sub4019, sub4108]
  rfl
theorem sub4110 (p : Pattern) : d107 (change p 10000 (some 160)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 160)) else d5 (change p 10000 (some 160))) = d107 p
  rw [sub4109, sub4108]
  rfl
theorem sub4111 (p : Pattern) : d125 (change p 10000 (some 160)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d107 (change p 10000 (some 160))) = d125 p
  rw [sub4019, sub4110]
  rfl
theorem sub4112 (p : Pattern) : d126 (change p 10000 (some 160)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 160)) else d124 (change p 10000 (some 160))) = d126 p
  rw [sub4111, sub4107]
  rfl
theorem sub4113 (p : Pattern) : d127 (change p 10000 (some 160)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 160)) else d123 (change p 10000 (some 160))) = d127 p
  rw [sub4112, sub4106]
  rfl
theorem sub4114 (p : Pattern) : d128 (change p 10000 (some 160)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d70 (change p 10000 (some 160))) = d128 p
  rw [sub4019, sub4061]
  rfl
theorem sub4115 (p : Pattern) : d129 (change p 10000 (some 160)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 160)) else d126 (change p 10000 (some 160))) = d129 p
  rw [sub4114, sub4112]
  rfl
theorem sub4116 (p : Pattern) : d130 (change p 10000 (some 160)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 160)) else d127 (change p 10000 (some 160))) = d130 p
  rw [sub4115, sub4113]
  rfl
theorem sub4117 (p : Pattern) : d131 (change p 10000 (some 160)) = d130 p := by
  change d130 (change p 10000 (some 160)) = d130 p
  exact sub4116 p
theorem sub4118 (p : Pattern) : d139 (change p 10000 (some 160)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d116 (change p 10000 (some 160))) = d139 p
  rw [sub4019, sub4098]
  rfl
theorem sub4119 (p : Pattern) : d140 (change p 10000 (some 160)) = d140 p := by
  change (if p 163 then d139 (change p 10000 (some 160)) else d122 (change p 10000 (some 160))) = d140 p
  rw [sub4118, sub4105]
  rfl
theorem sub4120 (p : Pattern) : d141 (change p 10000 (some 160)) = d141 p := by
  change (if p 163 then d70 (change p 10000 (some 160)) else d125 (change p 10000 (some 160))) = d141 p
  rw [sub4061, sub4111]
  rfl
theorem sub4121 (p : Pattern) : d142 (change p 10000 (some 160)) = d142 p := by
  change (if p 162 then d141 (change p 10000 (some 160)) else d140 (change p 10000 (some 160))) = d142 p
  rw [sub4120, sub4119]
  rfl
theorem sub4122 (p : Pattern) : d143 (change p 10000 (some 160)) = d143 p := by
  change (if p 163 then d72 (change p 10000 (some 160)) else d125 (change p 10000 (some 160))) = d143 p
  rw [sub4063, sub4111]
  rfl
theorem sub4123 (p : Pattern) : d144 (change p 10000 (some 160)) = d144 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d143 (change p 10000 (some 160))) = d144 p
  rw [sub4019, sub4122]
  rfl
theorem sub4124 (p : Pattern) : d145 (change p 10000 (some 160)) = d145 p := by
  change (if p 161 then d144 (change p 10000 (some 160)) else d142 (change p 10000 (some 160))) = d145 p
  rw [sub4123, sub4121]
  rfl
theorem sub4125 (p : Pattern) : d146 (change p 10000 (some 160)) = d145 p := by
  change d145 (change p 10000 (some 160)) = d145 p
  exact sub4124 p
theorem sub4126 (p : Pattern) : d147 (change p 10000 (some 160)) = d4123 p := by
  change (if p 141 then d146 (change p 10000 (some 160)) else d131 (change p 10000 (some 160))) = d4123 p
  rw [sub4125, sub4117]
  rfl
theorem sub4127 (p : Pattern) : d132 (change p 10000 (some 160)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 160)) else d116 (change p 10000 (some 160))) = d132 p
  rw [sub4099, sub4098]
  rfl
theorem sub4128 (p : Pattern) : d148 (change p 10000 (some 160)) = d148 p := by
  change (if p 182 then d121 (change p 10000 (some 160)) else d120 (change p 10000 (some 160))) = d148 p
  rw [sub4104, sub4103]
  rfl
theorem sub4129 (p : Pattern) : d149 (change p 10000 (some 160)) = d149 p := by
  change (if p 163 then d148 (change p 10000 (some 160)) else d132 (change p 10000 (some 160))) = d149 p
  rw [sub4128, sub4127]
  rfl
theorem sub4130 (p : Pattern) : d150 (change p 10000 (some 160)) = d150 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d149 (change p 10000 (some 160))) = d150 p
  rw [sub4019, sub4129]
  rfl
theorem sub4131 (p : Pattern) : d151 (change p 10000 (some 160)) = d151 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d150 (change p 10000 (some 160))) = d151 p
  rw [sub4019, sub4130]
  rfl
theorem sub4132 (p : Pattern) : d152 (change p 10000 (some 160)) = d151 p := by
  change d151 (change p 10000 (some 160)) = d151 p
  exact sub4131 p
theorem sub4133 (p : Pattern) : d153 (change p 10000 (some 160)) = d153 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d148 (change p 10000 (some 160))) = d153 p
  rw [sub4019, sub4128]
  rfl
theorem sub4134 (p : Pattern) : d154 (change p 10000 (some 160)) = d154 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d153 (change p 10000 (some 160))) = d154 p
  rw [sub4019, sub4133]
  rfl
theorem sub4135 (p : Pattern) : d155 (change p 10000 (some 160)) = d155 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d154 (change p 10000 (some 160))) = d155 p
  rw [sub4019, sub4134]
  rfl
theorem sub4136 (p : Pattern) : d156 (change p 10000 (some 160)) = d155 p := by
  change d155 (change p 10000 (some 160)) = d155 p
  exact sub4135 p
theorem sub4137 (p : Pattern) : d157 (change p 10000 (some 160)) = d4407 p := by
  change (if p 141 then d156 (change p 10000 (some 160)) else d152 (change p 10000 (some 160))) = d4407 p
  rw [sub4136, sub4132]
  rfl
theorem sub4138 (p : Pattern) : d158 (change p 10000 (some 160)) = d4408 p := by
  change (if p 138 then d157 (change p 10000 (some 160)) else d147 (change p 10000 (some 160))) = d4408 p
  rw [sub4137, sub4126]
  rfl
theorem sub4139 (p : Pattern) : d161 (change p 10000 (some 160)) = d12 p := by
  change d12 (change p 10000 (some 160)) = d12 p
  exact sub4019 p
theorem sub4140 (p : Pattern) : d162 (change p 10000 (some 160)) = d12 p := by
  change (if p 141 then d12 (change p 10000 (some 160)) else d161 (change p 10000 (some 160))) = d12 p
  rw [sub4019, sub4139]
  simp only [ite_self]
theorem sub4141 (p : Pattern) : d163 (change p 10000 (some 160)) = d4409 p := by
  change (if p 138 then d162 (change p 10000 (some 160)) else d157 (change p 10000 (some 160))) = d4409 p
  rw [sub4140, sub4137]
  rfl
theorem sub4142 (p : Pattern) : d164 (change p 10000 (some 160)) = d4410 p := by
  change (if p 116 then d163 (change p 10000 (some 160)) else d158 (change p 10000 (some 160))) = d4410 p
  rw [sub4141, sub4138]
  rfl
theorem sub4143 (p : Pattern) : d165 (change p 10000 (some 160)) = d4409 p := by
  change (if p 138 then d12 (change p 10000 (some 160)) else d157 (change p 10000 (some 160))) = d4409 p
  rw [sub4019, sub4137]
  rfl
theorem sub4144 (p : Pattern) : d166 (change p 10000 (some 160)) = d4410 p := by
  change (if p 116 then d165 (change p 10000 (some 160)) else d158 (change p 10000 (some 160))) = d4410 p
  rw [sub4143, sub4138]
  rfl
theorem sub4145 (p : Pattern) : d167 (change p 10000 (some 160)) = d4410 p := by
  change (if p 115 then d166 (change p 10000 (some 160)) else d164 (change p 10000 (some 160))) = d4410 p
  rw [sub4144, sub4142]
  simp only [ite_self]
theorem sub4146 (p : Pattern) : d168 (change p 10000 (some 160)) = d4411 p := by
  change (if p 71 then d167 (change p 10000 (some 160)) else d101 (change p 10000 (some 160))) = d4411 p
  rw [sub4145, sub4092]
  rfl
theorem sub4147 (p : Pattern) : d169 (change p 10000 (some 160)) = d4412 p := by
  change (if p 49 then d168 (change p 10000 (some 160)) else d101 (change p 10000 (some 160))) = d4412 p
  rw [sub4146, sub4092]
  rfl
theorem sub4148 (p : Pattern) : d170 (change p 10000 (some 160)) = d170 p := by
  change (if p 182 then d36 (change p 10000 (some 160)) else d31 (change p 10000 (some 160))) = d170 p
  rw [sub4030, sub4024]
  rfl
theorem sub4149 (p : Pattern) : d171 (change p 10000 (some 160)) = d171 p := by
  change (if p 163 then d170 (change p 10000 (some 160)) else d53 (change p 10000 (some 160))) = d171 p
  rw [sub4148, sub4069]
  rfl
theorem sub4150 (p : Pattern) : d172 (change p 10000 (some 160)) = d172 p := by
  change (if p 182 then d41 (change p 10000 (some 160)) else d31 (change p 10000 (some 160))) = d172 p
  rw [sub4036, sub4024]
  rfl
theorem sub4151 (p : Pattern) : d173 (change p 10000 (some 160)) = d173 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d35 (change p 10000 (some 160))) = d173 p
  rw [sub4019, sub4029]
  rfl
theorem sub4152 (p : Pattern) : d174 (change p 10000 (some 160)) = d174 p := by
  change (if p 163 then d173 (change p 10000 (some 160)) else d172 (change p 10000 (some 160))) = d174 p
  rw [sub4151, sub4150]
  rfl
theorem sub4153 (p : Pattern) : d175 (change p 10000 (some 160)) = d175 p := by
  change (if p 162 then d174 (change p 10000 (some 160)) else d171 (change p 10000 (some 160))) = d175 p
  rw [sub4152, sub4149]
  rfl
theorem sub4154 (p : Pattern) : d176 (change p 10000 (some 160)) = d176 p := by
  change (if p 163 then d173 (change p 10000 (some 160)) else d66 (change p 10000 (some 160))) = d176 p
  rw [sub4151, sub4054]
  rfl
theorem sub4155 (p : Pattern) : d177 (change p 10000 (some 160)) = d177 p := by
  change (if p 162 then d73 (change p 10000 (some 160)) else d176 (change p 10000 (some 160))) = d177 p
  rw [sub4064, sub4154]
  rfl
theorem sub4156 (p : Pattern) : d178 (change p 10000 (some 160)) = d178 p := by
  change (if p 161 then d177 (change p 10000 (some 160)) else d175 (change p 10000 (some 160))) = d178 p
  rw [sub4155, sub4153]
  rfl
theorem sub4157 (p : Pattern) : d179 (change p 10000 (some 160)) = d178 p := by
  change d178 (change p 10000 (some 160)) = d178 p
  exact sub4156 p
theorem sub4158 (p : Pattern) : d180 (change p 10000 (some 160)) = d180 p := by
  change (if p 163 then d43 (change p 10000 (some 160)) else d170 (change p 10000 (some 160))) = d180 p
  rw [sub4041, sub4148]
  rfl
theorem sub4159 (p : Pattern) : d181 (change p 10000 (some 160)) = d181 p := by
  change (if p 163 then d72 (change p 10000 (some 160)) else d173 (change p 10000 (some 160))) = d181 p
  rw [sub4063, sub4151]
  rfl
theorem sub4160 (p : Pattern) : d182 (change p 10000 (some 160)) = d182 p := by
  change (if p 162 then d181 (change p 10000 (some 160)) else d180 (change p 10000 (some 160))) = d182 p
  rw [sub4159, sub4158]
  rfl
theorem sub4161 (p : Pattern) : d183 (change p 10000 (some 160)) = d183 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d173 (change p 10000 (some 160))) = d183 p
  rw [sub4019, sub4151]
  rfl
theorem sub4162 (p : Pattern) : d184 (change p 10000 (some 160)) = d184 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d183 (change p 10000 (some 160))) = d184 p
  rw [sub4019, sub4161]
  rfl
theorem sub4163 (p : Pattern) : d185 (change p 10000 (some 160)) = d185 p := by
  change (if p 161 then d184 (change p 10000 (some 160)) else d182 (change p 10000 (some 160))) = d185 p
  rw [sub4162, sub4160]
  rfl
theorem sub4164 (p : Pattern) : d186 (change p 10000 (some 160)) = d185 p := by
  change d185 (change p 10000 (some 160)) = d185 p
  exact sub4163 p
theorem sub4165 (p : Pattern) : d187 (change p 10000 (some 160)) = d4413 p := by
  change (if p 141 then d186 (change p 10000 (some 160)) else d179 (change p 10000 (some 160))) = d4413 p
  rw [sub4164, sub4157]
  rfl
theorem sub4166 (p : Pattern) : d19 (change p 10000 (some 160)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d18 (change p 10000 (some 160))) = d19 p
  rw [sub4019, sub4040]
  rfl
theorem sub4167 (p : Pattern) : d20 (change p 10000 (some 160)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 160)) else d18 (change p 10000 (some 160))) = d20 p
  rw [sub4166, sub4040]
  rfl
theorem sub4168 (p : Pattern) : d8 (change p 10000 (some 160)) = d8 p := by
  rfl
theorem sub4169 (p : Pattern) : d190 (change p 10000 (some 160)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d8 (change p 10000 (some 160))) = d190 p
  rw [sub4019, sub4168]
  rfl
theorem sub4170 (p : Pattern) : d191 (change p 10000 (some 160)) = d191 p := by
  change (if p 246 then d190 (change p 10000 (some 160)) else d8 (change p 10000 (some 160))) = d191 p
  rw [sub4169, sub4168]
  rfl
theorem sub4171 (p : Pattern) : d192 (change p 10000 (some 160)) = d192 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d191 (change p 10000 (some 160))) = d192 p
  rw [sub4019, sub4170]
  rfl
theorem sub4172 (p : Pattern) : d193 (change p 10000 (some 160)) = d193 p := by
  change (if p 182 then d192 (change p 10000 (some 160)) else d191 (change p 10000 (some 160))) = d193 p
  rw [sub4171, sub4170]
  rfl
theorem sub4173 (p : Pattern) : d194 (change p 10000 (some 160)) = d194 p := by
  change (if p 163 then d193 (change p 10000 (some 160)) else d20 (change p 10000 (some 160))) = d194 p
  rw [sub4172, sub4167]
  rfl
theorem sub4174 (p : Pattern) : d195 (change p 10000 (some 160)) = d195 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d194 (change p 10000 (some 160))) = d195 p
  rw [sub4019, sub4173]
  rfl
theorem sub4175 (p : Pattern) : d196 (change p 10000 (some 160)) = d196 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d195 (change p 10000 (some 160))) = d196 p
  rw [sub4019, sub4174]
  rfl
theorem sub4176 (p : Pattern) : d197 (change p 10000 (some 160)) = d196 p := by
  change d196 (change p 10000 (some 160)) = d196 p
  exact sub4175 p
theorem sub4177 (p : Pattern) : d201 (change p 10000 (some 160)) = d201 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d193 (change p 10000 (some 160))) = d201 p
  rw [sub4019, sub4172]
  rfl
theorem sub4178 (p : Pattern) : d202 (change p 10000 (some 160)) = d202 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d201 (change p 10000 (some 160))) = d202 p
  rw [sub4019, sub4177]
  rfl
theorem sub4179 (p : Pattern) : d203 (change p 10000 (some 160)) = d203 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d202 (change p 10000 (some 160))) = d203 p
  rw [sub4019, sub4178]
  rfl
theorem sub4180 (p : Pattern) : d204 (change p 10000 (some 160)) = d203 p := by
  change d203 (change p 10000 (some 160)) = d203 p
  exact sub4179 p
theorem sub4181 (p : Pattern) : d205 (change p 10000 (some 160)) = d4414 p := by
  change (if p 141 then d204 (change p 10000 (some 160)) else d197 (change p 10000 (some 160))) = d4414 p
  rw [sub4180, sub4176]
  rfl
theorem sub4182 (p : Pattern) : d206 (change p 10000 (some 160)) = d4415 p := by
  change (if p 138 then d205 (change p 10000 (some 160)) else d187 (change p 10000 (some 160))) = d4415 p
  rw [sub4181, sub4165]
  rfl
theorem sub4183 (p : Pattern) : d207 (change p 10000 (some 160)) = d4416 p := by
  change (if p 138 then d12 (change p 10000 (some 160)) else d205 (change p 10000 (some 160))) = d4416 p
  rw [sub4019, sub4181]
  rfl
theorem sub4184 (p : Pattern) : d208 (change p 10000 (some 160)) = d4417 p := by
  change (if p 116 then d207 (change p 10000 (some 160)) else d206 (change p 10000 (some 160))) = d4417 p
  rw [sub4183, sub4182]
  rfl
theorem sub4185 (p : Pattern) : d209 (change p 10000 (some 160)) = d4418 p := by
  change (if p 115 then d208 (change p 10000 (some 160)) else d98 (change p 10000 (some 160))) = d4418 p
  rw [sub4184, sub4089]
  rfl
theorem sub4186 (p : Pattern) : d210 (change p 10000 (some 160)) = d4419 p := by
  change (if p 71 then d209 (change p 10000 (some 160)) else d101 (change p 10000 (some 160))) = d4419 p
  rw [sub4185, sub4092]
  rfl
theorem sub4187 (p : Pattern) : d215 (change p 10000 (some 160)) = d215 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d125 (change p 10000 (some 160))) = d215 p
  rw [sub4019, sub4111]
  rfl
theorem sub4188 (p : Pattern) : d216 (change p 10000 (some 160)) = d216 p := by
  change (if p 162 then d215 (change p 10000 (some 160)) else d140 (change p 10000 (some 160))) = d216 p
  rw [sub4187, sub4119]
  rfl
theorem sub4189 (p : Pattern) : d217 (change p 10000 (some 160)) = d217 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d215 (change p 10000 (some 160))) = d217 p
  rw [sub4019, sub4187]
  rfl
theorem sub4190 (p : Pattern) : d218 (change p 10000 (some 160)) = d218 p := by
  change (if p 161 then d217 (change p 10000 (some 160)) else d216 (change p 10000 (some 160))) = d218 p
  rw [sub4189, sub4188]
  rfl
theorem sub4191 (p : Pattern) : d219 (change p 10000 (some 160)) = d218 p := by
  change d218 (change p 10000 (some 160)) = d218 p
  exact sub4190 p
theorem sub4192 (p : Pattern) : d220 (change p 10000 (some 160)) = d4132 p := by
  change (if p 141 then d219 (change p 10000 (some 160)) else d131 (change p 10000 (some 160))) = d4132 p
  rw [sub4191, sub4117]
  rfl
theorem sub4193 (p : Pattern) : d221 (change p 10000 (some 160)) = d155 p := by
  change d155 (change p 10000 (some 160)) = d155 p
  exact sub4135 p
theorem sub4194 (p : Pattern) : d222 (change p 10000 (some 160)) = d4407 p := by
  change (if p 141 then d221 (change p 10000 (some 160)) else d152 (change p 10000 (some 160))) = d4407 p
  rw [sub4193, sub4132]
  rfl
theorem sub4195 (p : Pattern) : d223 (change p 10000 (some 160)) = d4420 p := by
  change (if p 138 then d222 (change p 10000 (some 160)) else d220 (change p 10000 (some 160))) = d4420 p
  rw [sub4194, sub4192]
  rfl
theorem sub4196 (p : Pattern) : d224 (change p 10000 (some 160)) = d4409 p := by
  change (if p 138 then d162 (change p 10000 (some 160)) else d222 (change p 10000 (some 160))) = d4409 p
  rw [sub4140, sub4194]
  rfl
theorem sub4197 (p : Pattern) : d225 (change p 10000 (some 160)) = d4421 p := by
  change (if p 116 then d224 (change p 10000 (some 160)) else d223 (change p 10000 (some 160))) = d4421 p
  rw [sub4196, sub4195]
  rfl
theorem sub4198 (p : Pattern) : d226 (change p 10000 (some 160)) = d226 p := by
  change (if p 182 then d121 (change p 10000 (some 160)) else d116 (change p 10000 (some 160))) = d226 p
  rw [sub4104, sub4098]
  rfl
theorem sub4199 (p : Pattern) : d227 (change p 10000 (some 160)) = d227 p := by
  change (if p 163 then d226 (change p 10000 (some 160)) else d132 (change p 10000 (some 160))) = d227 p
  rw [sub4198, sub4127]
  rfl
end NetHack.Sokoban22Refined85
