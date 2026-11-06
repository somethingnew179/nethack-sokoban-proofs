/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions34
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4200 (p : Pattern) : d228 (change p 10000 (some 160)) = d228 p := by
  change (if p 162 then d215 (change p 10000 (some 160)) else d227 (change p 10000 (some 160))) = d228 p
  rw [sub4187, sub4199]
  rfl
theorem sub4201 (p : Pattern) : d229 (change p 10000 (some 160)) = d229 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d120 (change p 10000 (some 160))) = d229 p
  rw [sub4019, sub4103]
  rfl
theorem sub4202 (p : Pattern) : d230 (change p 10000 (some 160)) = d230 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d229 (change p 10000 (some 160))) = d230 p
  rw [sub4019, sub4201]
  rfl
theorem sub4203 (p : Pattern) : d231 (change p 10000 (some 160)) = d231 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d230 (change p 10000 (some 160))) = d231 p
  rw [sub4019, sub4202]
  rfl
theorem sub4204 (p : Pattern) : d232 (change p 10000 (some 160)) = d232 p := by
  change (if p 161 then d231 (change p 10000 (some 160)) else d228 (change p 10000 (some 160))) = d232 p
  rw [sub4203, sub4200]
  rfl
theorem sub4205 (p : Pattern) : d233 (change p 10000 (some 160)) = d232 p := by
  change d232 (change p 10000 (some 160)) = d232 p
  exact sub4204 p
theorem sub4206 (p : Pattern) : d234 (change p 10000 (some 160)) = d234 p := by
  change (if p 182 then d121 (change p 10000 (some 160)) else d107 (change p 10000 (some 160))) = d234 p
  rw [sub4104, sub4110]
  rfl
theorem sub4207 (p : Pattern) : d235 (change p 10000 (some 160)) = d235 p := by
  change (if p 163 then d125 (change p 10000 (some 160)) else d234 (change p 10000 (some 160))) = d235 p
  rw [sub4111, sub4206]
  rfl
theorem sub4208 (p : Pattern) : d236 (change p 10000 (some 160)) = d236 p := by
  change (if p 162 then d230 (change p 10000 (some 160)) else d235 (change p 10000 (some 160))) = d236 p
  rw [sub4202, sub4207]
  rfl
theorem sub4209 (p : Pattern) : d237 (change p 10000 (some 160)) = d237 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d49 (change p 10000 (some 160))) = d237 p
  rw [sub4019, sub4050]
  rfl
theorem sub4210 (p : Pattern) : d238 (change p 10000 (some 160)) = d238 p := by
  change (if p 161 then d237 (change p 10000 (some 160)) else d236 (change p 10000 (some 160))) = d238 p
  rw [sub4209, sub4208]
  rfl
theorem sub4211 (p : Pattern) : d239 (change p 10000 (some 160)) = d238 p := by
  change d238 (change p 10000 (some 160)) = d238 p
  exact sub4210 p
theorem sub4212 (p : Pattern) : d240 (change p 10000 (some 160)) = d4422 p := by
  change (if p 141 then d239 (change p 10000 (some 160)) else d233 (change p 10000 (some 160))) = d4422 p
  rw [sub4211, sub4205]
  rfl
theorem sub4213 (p : Pattern) : d244 (change p 10000 (some 160)) = d155 p := by
  change d155 (change p 10000 (some 160)) = d155 p
  exact sub4135 p
theorem sub4214 (p : Pattern) : d25 (change p 10000 (some 160)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d24 (change p 10000 (some 160))) = d25 p
  rw [sub4019, sub4048]
  rfl
theorem sub4215 (p : Pattern) : d26 (change p 10000 (some 160)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 160)) else d24 (change p 10000 (some 160))) = d26 p
  rw [sub4214, sub4048]
  rfl
theorem sub4216 (p : Pattern) : d27 (change p 10000 (some 160)) = d27 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d26 (change p 10000 (some 160))) = d27 p
  rw [sub4019, sub4215]
  rfl
theorem sub4217 (p : Pattern) : d247 (change p 10000 (some 160)) = d247 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d27 (change p 10000 (some 160))) = d247 p
  rw [sub4019, sub4216]
  rfl
theorem sub4218 (p : Pattern) : d248 (change p 10000 (some 160)) = d248 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d247 (change p 10000 (some 160))) = d248 p
  rw [sub4019, sub4217]
  rfl
theorem sub4219 (p : Pattern) : d249 (change p 10000 (some 160)) = d248 p := by
  change d248 (change p 10000 (some 160)) = d248 p
  exact sub4218 p
theorem sub4220 (p : Pattern) : d250 (change p 10000 (some 160)) = d4423 p := by
  change (if p 141 then d249 (change p 10000 (some 160)) else d244 (change p 10000 (some 160))) = d4423 p
  rw [sub4219, sub4213]
  rfl
theorem sub4221 (p : Pattern) : d251 (change p 10000 (some 160)) = d4424 p := by
  change (if p 138 then d250 (change p 10000 (some 160)) else d240 (change p 10000 (some 160))) = d4424 p
  rw [sub4220, sub4212]
  rfl
theorem sub4222 (p : Pattern) : d257 (change p 10000 (some 160)) = d257 p := by
  change (if p 163 then d62 (change p 10000 (some 160)) else d148 (change p 10000 (some 160))) = d257 p
  rw [sub4072, sub4128]
  rfl
theorem sub4223 (p : Pattern) : d258 (change p 10000 (some 160)) = d258 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d257 (change p 10000 (some 160))) = d258 p
  rw [sub4019, sub4222]
  rfl
theorem sub4224 (p : Pattern) : d259 (change p 10000 (some 160)) = d259 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d258 (change p 10000 (some 160))) = d259 p
  rw [sub4019, sub4223]
  rfl
theorem sub4225 (p : Pattern) : d260 (change p 10000 (some 160)) = d259 p := by
  change d259 (change p 10000 (some 160)) = d259 p
  exact sub4224 p
theorem sub4226 (p : Pattern) : d261 (change p 10000 (some 160)) = d4425 p := by
  change (if p 141 then d249 (change p 10000 (some 160)) else d260 (change p 10000 (some 160))) = d4425 p
  rw [sub4219, sub4225]
  rfl
theorem sub4227 (p : Pattern) : d262 (change p 10000 (some 160)) = d4426 p := by
  change (if p 138 then d12 (change p 10000 (some 160)) else d261 (change p 10000 (some 160))) = d4426 p
  rw [sub4019, sub4226]
  rfl
theorem sub4228 (p : Pattern) : d263 (change p 10000 (some 160)) = d4427 p := by
  change (if p 116 then d262 (change p 10000 (some 160)) else d251 (change p 10000 (some 160))) = d4427 p
  rw [sub4227, sub4221]
  rfl
theorem sub4229 (p : Pattern) : d264 (change p 10000 (some 160)) = d4428 p := by
  change (if p 115 then d263 (change p 10000 (some 160)) else d225 (change p 10000 (some 160))) = d4428 p
  rw [sub4228, sub4197]
  rfl
theorem sub4230 (p : Pattern) : d265 (change p 10000 (some 160)) = d4429 p := by
  change (if p 71 then d264 (change p 10000 (some 160)) else d101 (change p 10000 (some 160))) = d4429 p
  rw [sub4229, sub4092]
  rfl
theorem sub4231 (p : Pattern) : d266 (change p 10000 (some 160)) = d4430 p := by
  change (if p 49 then d265 (change p 10000 (some 160)) else d210 (change p 10000 (some 160))) = d4430 p
  rw [sub4230, sub4186]
  rfl
theorem sub4232 (p : Pattern) : d267 (change p 10000 (some 160)) = d4431 p := by
  change (if p 48 then d266 (change p 10000 (some 160)) else d169 (change p 10000 (some 160))) = d4431 p
  rw [sub4231, sub4147]
  rfl
theorem sub4233 (p : Pattern) : d0 (change p 160 (some 161)) = d0 p := by
  rfl
theorem sub4234 (p : Pattern) : d12 (change p 160 (some 161)) = d12 p := by
  rfl
theorem sub4235 (p : Pattern) : d13 (change p 160 (some 161)) = d13 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d0 (change p 160 (some 161))) = d13 p
  rw [sub4234, sub4233]
  rfl
theorem sub4236 (p : Pattern) : d14 (change p 160 (some 161)) = d14 p := by
  change (if p 246 then d13 (change p 160 (some 161)) else d0 (change p 160 (some 161))) = d14 p
  rw [sub4235, sub4233]
  rfl
theorem sub4237 (p : Pattern) : d15 (change p 160 (some 161)) = d15 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d14 (change p 160 (some 161))) = d15 p
  rw [sub4234, sub4236]
  rfl
theorem sub4238 (p : Pattern) : d16 (change p 160 (some 161)) = d16 p := by
  change (if p 182 then d15 (change p 160 (some 161)) else d14 (change p 160 (some 161))) = d16 p
  rw [sub4237, sub4236]
  rfl
theorem sub4239 (p : Pattern) : d4 (change p 160 (some 161)) = d4 p := by
  rfl
theorem sub4240 (p : Pattern) : d17 (change p 160 (some 161)) = d17 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d4 (change p 160 (some 161))) = d17 p
  rw [sub4234, sub4239]
  rfl
theorem sub4241 (p : Pattern) : d18 (change p 160 (some 161)) = d18 p := by
  change (if p 246 then d17 (change p 160 (some 161)) else d4 (change p 160 (some 161))) = d18 p
  rw [sub4240, sub4239]
  rfl
theorem sub4242 (p : Pattern) : d19 (change p 160 (some 161)) = d19 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d18 (change p 160 (some 161))) = d19 p
  rw [sub4234, sub4241]
  rfl
theorem sub4243 (p : Pattern) : d20 (change p 160 (some 161)) = d20 p := by
  change (if p 182 then d19 (change p 160 (some 161)) else d18 (change p 160 (some 161))) = d20 p
  rw [sub4242, sub4241]
  rfl
theorem sub4244 (p : Pattern) : d21 (change p 160 (some 161)) = d21 p := by
  change (if p 163 then d20 (change p 160 (some 161)) else d16 (change p 160 (some 161))) = d21 p
  rw [sub4243, sub4238]
  rfl
theorem sub4245 (p : Pattern) : d9 (change p 160 (some 161)) = d9 p := by
  rfl
theorem sub4246 (p : Pattern) : d23 (change p 160 (some 161)) = d23 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d9 (change p 160 (some 161))) = d23 p
  rw [sub4234, sub4245]
  rfl
theorem sub4247 (p : Pattern) : d24 (change p 160 (some 161)) = d24 p := by
  change (if p 246 then d23 (change p 160 (some 161)) else d9 (change p 160 (some 161))) = d24 p
  rw [sub4246, sub4245]
  rfl
theorem sub4248 (p : Pattern) : d25 (change p 160 (some 161)) = d25 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d24 (change p 160 (some 161))) = d25 p
  rw [sub4234, sub4247]
  rfl
theorem sub4249 (p : Pattern) : d26 (change p 160 (some 161)) = d26 p := by
  change (if p 182 then d25 (change p 160 (some 161)) else d24 (change p 160 (some 161))) = d26 p
  rw [sub4248, sub4247]
  rfl
theorem sub4250 (p : Pattern) : d27 (change p 160 (some 161)) = d27 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d26 (change p 160 (some 161))) = d27 p
  rw [sub4234, sub4249]
  rfl
theorem sub4251 (p : Pattern) : d28 (change p 160 (some 161)) = d28 p := by
  change (if p 162 then d27 (change p 160 (some 161)) else d21 (change p 160 (some 161))) = d28 p
  rw [sub4250, sub4244]
  rfl
theorem sub4252 (p : Pattern) : d29 (change p 160 (some 161)) = d28 p := by
  change d28 (change p 160 (some 161)) = d28 p
  exact sub4251 p
theorem sub4253 (p : Pattern) : d710 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4254 (p : Pattern) : d10 (change p 160 (some 161)) = d10 p := by
  rfl
theorem sub4255 (p : Pattern) : d57 (change p 160 (some 161)) = d57 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d10 (change p 160 (some 161))) = d57 p
  rw [sub4234, sub4254]
  rfl
theorem sub4256 (p : Pattern) : d58 (change p 160 (some 161)) = d58 p := by
  change (if p 246 then d57 (change p 160 (some 161)) else d10 (change p 160 (some 161))) = d58 p
  rw [sub4255, sub4254]
  rfl
theorem sub4257 (p : Pattern) : d59 (change p 160 (some 161)) = d59 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d58 (change p 160 (some 161))) = d59 p
  rw [sub4234, sub4256]
  rfl
theorem sub4258 (p : Pattern) : d60 (change p 160 (some 161)) = d60 p := by
  change (if p 182 then d59 (change p 160 (some 161)) else d58 (change p 160 (some 161))) = d60 p
  rw [sub4257, sub4256]
  rfl
theorem sub4259 (p : Pattern) : d61 (change p 160 (some 161)) = d61 p := by
  change (if p 163 then d60 (change p 160 (some 161)) else d20 (change p 160 (some 161))) = d61 p
  rw [sub4258, sub4243]
  rfl
theorem sub4260 (p : Pattern) : d11 (change p 160 (some 161)) = d11 p := by
  rfl
theorem sub4261 (p : Pattern) : d39 (change p 160 (some 161)) = d39 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d11 (change p 160 (some 161))) = d39 p
  rw [sub4234, sub4260]
  rfl
theorem sub4262 (p : Pattern) : d40 (change p 160 (some 161)) = d40 p := by
  change (if p 246 then d39 (change p 160 (some 161)) else d11 (change p 160 (some 161))) = d40 p
  rw [sub4261, sub4260]
  rfl
theorem sub4263 (p : Pattern) : d41 (change p 160 (some 161)) = d41 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d40 (change p 160 (some 161))) = d41 p
  rw [sub4234, sub4262]
  rfl
theorem sub4264 (p : Pattern) : d62 (change p 160 (some 161)) = d62 p := by
  change (if p 182 then d41 (change p 160 (some 161)) else d40 (change p 160 (some 161))) = d62 p
  rw [sub4263, sub4262]
  rfl
theorem sub4265 (p : Pattern) : d63 (change p 160 (some 161)) = d63 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d62 (change p 160 (some 161))) = d63 p
  rw [sub4234, sub4264]
  rfl
theorem sub4266 (p : Pattern) : d64 (change p 160 (some 161)) = d64 p := by
  change (if p 162 then d63 (change p 160 (some 161)) else d61 (change p 160 (some 161))) = d64 p
  rw [sub4265, sub4259]
  rfl
theorem sub4267 (p : Pattern) : d65 (change p 160 (some 161)) = d64 p := by
  change d64 (change p 160 (some 161)) = d64 p
  exact sub4266 p
theorem sub4268 (p : Pattern) : d711 (change p 160 (some 161)) = d64 p := by
  change d65 (change p 160 (some 161)) = d64 p
  exact sub4267 p
theorem sub4269 (p : Pattern) : d712 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d711 (change p 160 (some 161)) else d710 (change p 160 (some 161))) = d4433 p
  rw [sub4268, sub4253]
  rfl
theorem sub4270 (p : Pattern) : d713 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4271 (p : Pattern) : d714 (change p 160 (some 161)) = d64 p := by
  change d65 (change p 160 (some 161)) = d64 p
  exact sub4267 p
theorem sub4272 (p : Pattern) : d715 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d714 (change p 160 (some 161)) else d713 (change p 160 (some 161))) = d4433 p
  rw [sub4271, sub4270]
  rfl
theorem sub4273 (p : Pattern) : d716 (change p 160 (some 161)) = d4433 p := by
  change (if p 138 then d715 (change p 160 (some 161)) else d712 (change p 160 (some 161))) = d4433 p
  rw [sub4272, sub4269]
  simp only [ite_self]
theorem sub4274 (p : Pattern) : d717 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4275 (p : Pattern) : d718 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d714 (change p 160 (some 161)) else d717 (change p 160 (some 161))) = d4433 p
  rw [sub4271, sub4274]
  rfl
theorem sub4276 (p : Pattern) : d91 (change p 160 (some 161)) = d91 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d63 (change p 160 (some 161))) = d91 p
  rw [sub4234, sub4265]
  rfl
theorem sub4277 (p : Pattern) : d92 (change p 160 (some 161)) = d91 p := by
  change d91 (change p 160 (some 161)) = d91 p
  exact sub4276 p
theorem sub4278 (p : Pattern) : d719 (change p 160 (some 161)) = d91 p := by
  change d92 (change p 160 (some 161)) = d91 p
  exact sub4277 p
theorem sub4279 (p : Pattern) : d93 (change p 160 (some 161)) = d12 p := by
  change d12 (change p 160 (some 161)) = d12 p
  exact sub4234 p
theorem sub4280 (p : Pattern) : d95 (change p 160 (some 161)) = d12 p := by
  change d93 (change p 160 (some 161)) = d12 p
  exact sub4279 p
theorem sub4281 (p : Pattern) : d720 (change p 160 (some 161)) = d4434 p := by
  change (if p 141 then d95 (change p 160 (some 161)) else d719 (change p 160 (some 161))) = d4434 p
  rw [sub4280, sub4278]
  rfl
theorem sub4282 (p : Pattern) : d721 (change p 160 (some 161)) = d4435 p := by
  change (if p 138 then d720 (change p 160 (some 161)) else d718 (change p 160 (some 161))) = d4435 p
  rw [sub4281, sub4275]
  rfl
theorem sub4283 (p : Pattern) : d722 (change p 160 (some 161)) = d4436 p := by
  change (if p 116 then d721 (change p 160 (some 161)) else d716 (change p 160 (some 161))) = d4436 p
  rw [sub4282, sub4273]
  rfl
theorem sub4284 (p : Pattern) : d723 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4285 (p : Pattern) : d724 (change p 160 (some 161)) = d64 p := by
  change d65 (change p 160 (some 161)) = d64 p
  exact sub4267 p
theorem sub4286 (p : Pattern) : d725 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d724 (change p 160 (some 161)) else d723 (change p 160 (some 161))) = d4433 p
  rw [sub4285, sub4284]
  rfl
theorem sub4287 (p : Pattern) : d726 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4288 (p : Pattern) : d727 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d714 (change p 160 (some 161)) else d726 (change p 160 (some 161))) = d4433 p
  rw [sub4271, sub4287]
  rfl
theorem sub4289 (p : Pattern) : d728 (change p 160 (some 161)) = d4433 p := by
  change (if p 138 then d727 (change p 160 (some 161)) else d725 (change p 160 (some 161))) = d4433 p
  rw [sub4288, sub4286]
  simp only [ite_self]
theorem sub4290 (p : Pattern) : d729 (change p 160 (some 161)) = d4437 p := by
  change (if p 138 then d12 (change p 160 (some 161)) else d727 (change p 160 (some 161))) = d4437 p
  rw [sub4234, sub4288]
  rfl
theorem sub4291 (p : Pattern) : d730 (change p 160 (some 161)) = d4438 p := by
  change (if p 116 then d729 (change p 160 (some 161)) else d728 (change p 160 (some 161))) = d4438 p
  rw [sub4290, sub4289]
  rfl
theorem sub4292 (p : Pattern) : d731 (change p 160 (some 161)) = d4439 p := by
  change (if p 115 then d730 (change p 160 (some 161)) else d722 (change p 160 (some 161))) = d4439 p
  rw [sub4291, sub4283]
  rfl
theorem sub4293 (p : Pattern) : d732 (change p 160 (some 161)) = d28 p := by
  change d29 (change p 160 (some 161)) = d28 p
  exact sub4252 p
theorem sub4294 (p : Pattern) : d733 (change p 160 (some 161)) = d64 p := by
  change d65 (change p 160 (some 161)) = d64 p
  exact sub4267 p
theorem sub4295 (p : Pattern) : d734 (change p 160 (some 161)) = d4433 p := by
  change (if p 141 then d733 (change p 160 (some 161)) else d732 (change p 160 (some 161))) = d4433 p
  rw [sub4294, sub4293]
  rfl
theorem sub4296 (p : Pattern) : d735 (change p 160 (some 161)) = d4433 p := by
  change (if p 138 then d727 (change p 160 (some 161)) else d734 (change p 160 (some 161))) = d4433 p
  rw [sub4288, sub4295]
  simp only [ite_self]
theorem sub4297 (p : Pattern) : d736 (change p 160 (some 161)) = d4435 p := by
  change (if p 138 then d720 (change p 160 (some 161)) else d715 (change p 160 (some 161))) = d4435 p
  rw [sub4281, sub4272]
  rfl
theorem sub4298 (p : Pattern) : d737 (change p 160 (some 161)) = d4436 p := by
  change (if p 116 then d736 (change p 160 (some 161)) else d735 (change p 160 (some 161))) = d4436 p
  rw [sub4297, sub4296]
  rfl
theorem sub4299 (p : Pattern) : d738 (change p 160 (some 161)) = d4433 p := by
  change (if p 138 then d727 (change p 160 (some 161)) else d718 (change p 160 (some 161))) = d4433 p
  rw [sub4288, sub4275]
  simp only [ite_self]
theorem sub4300 (p : Pattern) : d739 (change p 160 (some 161)) = d4438 p := by
  change (if p 116 then d729 (change p 160 (some 161)) else d738 (change p 160 (some 161))) = d4438 p
  rw [sub4290, sub4299]
  rfl
theorem sub4301 (p : Pattern) : d740 (change p 160 (some 161)) = d4439 p := by
  change (if p 115 then d739 (change p 160 (some 161)) else d737 (change p 160 (some 161))) = d4439 p
  rw [sub4300, sub4298]
  rfl
theorem sub4302 (p : Pattern) : d741 (change p 160 (some 161)) = d4439 p := by
  change (if p 71 then d740 (change p 160 (some 161)) else d731 (change p 160 (some 161))) = d4439 p
  rw [sub4301, sub4292]
  simp only [ite_self]
theorem sub4303 (p : Pattern) : d1 (change p 160 (some 161)) = d1 p := by
  rfl
theorem sub4304 (p : Pattern) : d102 (change p 160 (some 161)) = d102 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d1 (change p 160 (some 161))) = d102 p
  rw [sub4234, sub4303]
  rfl
theorem sub4305 (p : Pattern) : d103 (change p 160 (some 161)) = d103 p := by
  change (if p 246 then d102 (change p 160 (some 161)) else d1 (change p 160 (some 161))) = d103 p
  rw [sub4304, sub4303]
  rfl
theorem sub4306 (p : Pattern) : d104 (change p 160 (some 161)) = d104 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d103 (change p 160 (some 161))) = d104 p
  rw [sub4234, sub4305]
  rfl
theorem sub4307 (p : Pattern) : d105 (change p 160 (some 161)) = d105 p := by
  change (if p 182 then d104 (change p 160 (some 161)) else d103 (change p 160 (some 161))) = d105 p
  rw [sub4306, sub4305]
  rfl
theorem sub4308 (p : Pattern) : d5 (change p 160 (some 161)) = d5 p := by
  rfl
theorem sub4309 (p : Pattern) : d106 (change p 160 (some 161)) = d106 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d5 (change p 160 (some 161))) = d106 p
  rw [sub4234, sub4308]
  rfl
theorem sub4310 (p : Pattern) : d107 (change p 160 (some 161)) = d107 p := by
  change (if p 246 then d106 (change p 160 (some 161)) else d5 (change p 160 (some 161))) = d107 p
  rw [sub4309, sub4308]
  rfl
theorem sub4311 (p : Pattern) : d108 (change p 160 (some 161)) = d108 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d107 (change p 160 (some 161))) = d108 p
  rw [sub4234, sub4310]
  rfl
theorem sub4312 (p : Pattern) : d109 (change p 160 (some 161)) = d109 p := by
  change (if p 182 then d108 (change p 160 (some 161)) else d107 (change p 160 (some 161))) = d109 p
  rw [sub4311, sub4310]
  rfl
theorem sub4313 (p : Pattern) : d110 (change p 160 (some 161)) = d110 p := by
  change (if p 163 then d109 (change p 160 (some 161)) else d105 (change p 160 (some 161))) = d110 p
  rw [sub4312, sub4307]
  rfl
theorem sub4314 (p : Pattern) : d112 (change p 160 (some 161)) = d112 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d60 (change p 160 (some 161))) = d112 p
  rw [sub4234, sub4258]
  rfl
theorem sub4315 (p : Pattern) : d113 (change p 160 (some 161)) = d113 p := by
  change (if p 162 then d112 (change p 160 (some 161)) else d110 (change p 160 (some 161))) = d113 p
  rw [sub4314, sub4313]
  rfl
theorem sub4316 (p : Pattern) : d114 (change p 160 (some 161)) = d113 p := by
  change d113 (change p 160 (some 161)) = d113 p
  exact sub4315 p
theorem sub4317 (p : Pattern) : d742 (change p 160 (some 161)) = d113 p := by
  change d114 (change p 160 (some 161)) = d113 p
  exact sub4316 p
theorem sub4318 (p : Pattern) : d136 (change p 160 (some 161)) = d136 p := by
  change (if p 163 then d62 (change p 160 (some 161)) else d109 (change p 160 (some 161))) = d136 p
  rw [sub4264, sub4312]
  rfl
theorem sub4319 (p : Pattern) : d137 (change p 160 (some 161)) = d137 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d136 (change p 160 (some 161))) = d137 p
  rw [sub4234, sub4318]
  rfl
end NetHack.Sokoban22Refined85
