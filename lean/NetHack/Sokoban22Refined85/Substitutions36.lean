/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions35
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4320 (p : Pattern) : d138 (change p 160 (some 161)) = d137 p := by
  change d137 (change p 160 (some 161)) = d137 p
  exact sub4319 p
theorem sub4321 (p : Pattern) : d743 (change p 160 (some 161)) = d137 p := by
  change d138 (change p 160 (some 161)) = d137 p
  exact sub4320 p
theorem sub4322 (p : Pattern) : d744 (change p 160 (some 161)) = d4440 p := by
  change (if p 141 then d743 (change p 160 (some 161)) else d742 (change p 160 (some 161))) = d4440 p
  rw [sub4321, sub4317]
  rfl
theorem sub4323 (p : Pattern) : d745 (change p 160 (some 161)) = d113 p := by
  change d114 (change p 160 (some 161)) = d113 p
  exact sub4316 p
theorem sub4324 (p : Pattern) : d746 (change p 160 (some 161)) = d137 p := by
  change d138 (change p 160 (some 161)) = d137 p
  exact sub4320 p
theorem sub4325 (p : Pattern) : d747 (change p 160 (some 161)) = d4440 p := by
  change (if p 141 then d746 (change p 160 (some 161)) else d745 (change p 160 (some 161))) = d4440 p
  rw [sub4324, sub4323]
  rfl
theorem sub4326 (p : Pattern) : d748 (change p 160 (some 161)) = d4440 p := by
  change (if p 138 then d747 (change p 160 (some 161)) else d744 (change p 160 (some 161))) = d4440 p
  rw [sub4325, sub4322]
  simp only [ite_self]
theorem sub4327 (p : Pattern) : d749 (change p 160 (some 161)) = d113 p := by
  change d114 (change p 160 (some 161)) = d113 p
  exact sub4316 p
theorem sub4328 (p : Pattern) : d750 (change p 160 (some 161)) = d4440 p := by
  change (if p 141 then d746 (change p 160 (some 161)) else d749 (change p 160 (some 161))) = d4440 p
  rw [sub4324, sub4327]
  rfl
theorem sub4329 (p : Pattern) : d160 (change p 160 (some 161)) = d12 p := by
  change d12 (change p 160 (some 161)) = d12 p
  exact sub4234 p
theorem sub4330 (p : Pattern) : d161 (change p 160 (some 161)) = d12 p := by
  change d160 (change p 160 (some 161)) = d12 p
  exact sub4329 p
theorem sub4331 (p : Pattern) : d162 (change p 160 (some 161)) = d12 p := by
  change (if p 141 then d12 (change p 160 (some 161)) else d161 (change p 160 (some 161))) = d12 p
  rw [sub4234, sub4330]
  simp only [ite_self]
theorem sub4332 (p : Pattern) : d751 (change p 160 (some 161)) = d4441 p := by
  change (if p 138 then d162 (change p 160 (some 161)) else d750 (change p 160 (some 161))) = d4441 p
  rw [sub4331, sub4328]
  rfl
theorem sub4333 (p : Pattern) : d752 (change p 160 (some 161)) = d4442 p := by
  change (if p 116 then d751 (change p 160 (some 161)) else d748 (change p 160 (some 161))) = d4442 p
  rw [sub4332, sub4326]
  rfl
theorem sub4334 (p : Pattern) : d753 (change p 160 (some 161)) = d113 p := by
  change d114 (change p 160 (some 161)) = d113 p
  exact sub4316 p
theorem sub4335 (p : Pattern) : d754 (change p 160 (some 161)) = d4440 p := by
  change (if p 141 then d746 (change p 160 (some 161)) else d753 (change p 160 (some 161))) = d4440 p
  rw [sub4324, sub4334]
  rfl
theorem sub4336 (p : Pattern) : d755 (change p 160 (some 161)) = d4440 p := by
  change (if p 138 then d747 (change p 160 (some 161)) else d754 (change p 160 (some 161))) = d4440 p
  rw [sub4325, sub4335]
  simp only [ite_self]
theorem sub4337 (p : Pattern) : d756 (change p 160 (some 161)) = d4441 p := by
  change (if p 138 then d12 (change p 160 (some 161)) else d747 (change p 160 (some 161))) = d4441 p
  rw [sub4234, sub4325]
  rfl
theorem sub4338 (p : Pattern) : d757 (change p 160 (some 161)) = d4442 p := by
  change (if p 116 then d756 (change p 160 (some 161)) else d755 (change p 160 (some 161))) = d4442 p
  rw [sub4337, sub4336]
  rfl
theorem sub4339 (p : Pattern) : d758 (change p 160 (some 161)) = d4442 p := by
  change (if p 115 then d757 (change p 160 (some 161)) else d752 (change p 160 (some 161))) = d4442 p
  rw [sub4338, sub4333]
  simp only [ite_self]
theorem sub4340 (p : Pattern) : d759 (change p 160 (some 161)) = d4443 p := by
  change (if p 71 then d758 (change p 160 (some 161)) else d731 (change p 160 (some 161))) = d4443 p
  rw [sub4339, sub4292]
  rfl
theorem sub4341 (p : Pattern) : d760 (change p 160 (some 161)) = d4444 p := by
  change (if p 49 then d759 (change p 160 (some 161)) else d741 (change p 160 (some 161))) = d4444 p
  rw [sub4340, sub4302]
  rfl
theorem sub4342 (p : Pattern) : d2 (change p 160 (some 161)) = d2 p := by
  rfl
theorem sub4343 (p : Pattern) : d30 (change p 160 (some 161)) = d30 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d2 (change p 160 (some 161))) = d30 p
  rw [sub4234, sub4342]
  rfl
theorem sub4344 (p : Pattern) : d31 (change p 160 (some 161)) = d31 p := by
  change (if p 246 then d30 (change p 160 (some 161)) else d2 (change p 160 (some 161))) = d31 p
  rw [sub4343, sub4342]
  rfl
theorem sub4345 (p : Pattern) : d32 (change p 160 (some 161)) = d32 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d31 (change p 160 (some 161))) = d32 p
  rw [sub4234, sub4344]
  rfl
theorem sub4346 (p : Pattern) : d53 (change p 160 (some 161)) = d53 p := by
  change (if p 182 then d32 (change p 160 (some 161)) else d31 (change p 160 (some 161))) = d53 p
  rw [sub4345, sub4344]
  rfl
theorem sub4347 (p : Pattern) : d6 (change p 160 (some 161)) = d6 p := by
  rfl
theorem sub4348 (p : Pattern) : d34 (change p 160 (some 161)) = d34 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d6 (change p 160 (some 161))) = d34 p
  rw [sub4234, sub4347]
  rfl
theorem sub4349 (p : Pattern) : d35 (change p 160 (some 161)) = d35 p := by
  change (if p 246 then d34 (change p 160 (some 161)) else d6 (change p 160 (some 161))) = d35 p
  rw [sub4348, sub4347]
  rfl
theorem sub4350 (p : Pattern) : d36 (change p 160 (some 161)) = d36 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d35 (change p 160 (some 161))) = d36 p
  rw [sub4234, sub4349]
  rfl
theorem sub4351 (p : Pattern) : d78 (change p 160 (some 161)) = d78 p := by
  change (if p 182 then d36 (change p 160 (some 161)) else d35 (change p 160 (some 161))) = d78 p
  rw [sub4350, sub4349]
  rfl
theorem sub4352 (p : Pattern) : d79 (change p 160 (some 161)) = d79 p := by
  change (if p 163 then d78 (change p 160 (some 161)) else d53 (change p 160 (some 161))) = d79 p
  rw [sub4351, sub4346]
  rfl
theorem sub4353 (p : Pattern) : d80 (change p 160 (some 161)) = d80 p := by
  change (if p 162 then d63 (change p 160 (some 161)) else d79 (change p 160 (some 161))) = d80 p
  rw [sub4265, sub4352]
  rfl
theorem sub4354 (p : Pattern) : d189 (change p 160 (some 161)) = d80 p := by
  change d80 (change p 160 (some 161)) = d80 p
  exact sub4353 p
theorem sub4355 (p : Pattern) : d761 (change p 160 (some 161)) = d80 p := by
  change d189 (change p 160 (some 161)) = d80 p
  exact sub4354 p
theorem sub4356 (p : Pattern) : d83 (change p 160 (some 161)) = d83 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d78 (change p 160 (some 161))) = d83 p
  rw [sub4234, sub4351]
  rfl
theorem sub4357 (p : Pattern) : d84 (change p 160 (some 161)) = d84 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d83 (change p 160 (some 161))) = d84 p
  rw [sub4234, sub4356]
  rfl
theorem sub4358 (p : Pattern) : d200 (change p 160 (some 161)) = d84 p := by
  change d84 (change p 160 (some 161)) = d84 p
  exact sub4357 p
theorem sub4359 (p : Pattern) : d762 (change p 160 (some 161)) = d84 p := by
  change d200 (change p 160 (some 161)) = d84 p
  exact sub4358 p
theorem sub4360 (p : Pattern) : d763 (change p 160 (some 161)) = d4445 p := by
  change (if p 141 then d762 (change p 160 (some 161)) else d761 (change p 160 (some 161))) = d4445 p
  rw [sub4359, sub4355]
  rfl
theorem sub4361 (p : Pattern) : d764 (change p 160 (some 161)) = d4446 p := by
  change (if p 138 then d763 (change p 160 (some 161)) else d718 (change p 160 (some 161))) = d4446 p
  rw [sub4360, sub4275]
  rfl
theorem sub4362 (p : Pattern) : d765 (change p 160 (some 161)) = d4447 p := by
  change (if p 138 then d12 (change p 160 (some 161)) else d763 (change p 160 (some 161))) = d4447 p
  rw [sub4234, sub4360]
  rfl
theorem sub4363 (p : Pattern) : d766 (change p 160 (some 161)) = d4448 p := by
  change (if p 116 then d765 (change p 160 (some 161)) else d764 (change p 160 (some 161))) = d4448 p
  rw [sub4362, sub4361]
  rfl
theorem sub4364 (p : Pattern) : d767 (change p 160 (some 161)) = d4449 p := by
  change (if p 115 then d766 (change p 160 (some 161)) else d737 (change p 160 (some 161))) = d4449 p
  rw [sub4363, sub4298]
  rfl
theorem sub4365 (p : Pattern) : d768 (change p 160 (some 161)) = d4450 p := by
  change (if p 71 then d767 (change p 160 (some 161)) else d731 (change p 160 (some 161))) = d4450 p
  rw [sub4364, sub4292]
  rfl
theorem sub4366 (p : Pattern) : d211 (change p 160 (some 161)) = d211 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d109 (change p 160 (some 161))) = d211 p
  rw [sub4234, sub4312]
  rfl
theorem sub4367 (p : Pattern) : d213 (change p 160 (some 161)) = d213 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d211 (change p 160 (some 161))) = d213 p
  rw [sub4234, sub4366]
  rfl
theorem sub4368 (p : Pattern) : d214 (change p 160 (some 161)) = d213 p := by
  change d213 (change p 160 (some 161)) = d213 p
  exact sub4367 p
theorem sub4369 (p : Pattern) : d769 (change p 160 (some 161)) = d213 p := by
  change d214 (change p 160 (some 161)) = d213 p
  exact sub4368 p
theorem sub4370 (p : Pattern) : d770 (change p 160 (some 161)) = d4451 p := by
  change (if p 141 then d769 (change p 160 (some 161)) else d742 (change p 160 (some 161))) = d4451 p
  rw [sub4369, sub4317]
  rfl
theorem sub4371 (p : Pattern) : d771 (change p 160 (some 161)) = d213 p := by
  change d214 (change p 160 (some 161)) = d213 p
  exact sub4368 p
theorem sub4372 (p : Pattern) : d772 (change p 160 (some 161)) = d4451 p := by
  change (if p 141 then d771 (change p 160 (some 161)) else d745 (change p 160 (some 161))) = d4451 p
  rw [sub4371, sub4323]
  rfl
theorem sub4373 (p : Pattern) : d773 (change p 160 (some 161)) = d4451 p := by
  change (if p 138 then d772 (change p 160 (some 161)) else d770 (change p 160 (some 161))) = d4451 p
  rw [sub4372, sub4370]
  simp only [ite_self]
theorem sub4374 (p : Pattern) : d774 (change p 160 (some 161)) = d4451 p := by
  change (if p 141 then d771 (change p 160 (some 161)) else d749 (change p 160 (some 161))) = d4451 p
  rw [sub4371, sub4327]
  rfl
theorem sub4375 (p : Pattern) : d775 (change p 160 (some 161)) = d4452 p := by
  change (if p 138 then d162 (change p 160 (some 161)) else d774 (change p 160 (some 161))) = d4452 p
  rw [sub4331, sub4374]
  rfl
theorem sub4376 (p : Pattern) : d776 (change p 160 (some 161)) = d4453 p := by
  change (if p 116 then d775 (change p 160 (some 161)) else d773 (change p 160 (some 161))) = d4453 p
  rw [sub4375, sub4373]
  rfl
theorem sub4377 (p : Pattern) : d777 (change p 160 (some 161)) = d4451 p := by
  change (if p 141 then d771 (change p 160 (some 161)) else d753 (change p 160 (some 161))) = d4451 p
  rw [sub4371, sub4334]
  rfl
theorem sub4378 (p : Pattern) : d243 (change p 160 (some 161)) = d137 p := by
  change d137 (change p 160 (some 161)) = d137 p
  exact sub4319 p
theorem sub4379 (p : Pattern) : d778 (change p 160 (some 161)) = d137 p := by
  change d243 (change p 160 (some 161)) = d137 p
  exact sub4378 p
theorem sub4380 (p : Pattern) : d7 (change p 160 (some 161)) = d7 p := by
  rfl
theorem sub4381 (p : Pattern) : d119 (change p 160 (some 161)) = d119 p := by
  change (if p 247 then d12 (change p 160 (some 161)) else d7 (change p 160 (some 161))) = d119 p
  rw [sub4234, sub4380]
  rfl
theorem sub4382 (p : Pattern) : d120 (change p 160 (some 161)) = d120 p := by
  change (if p 246 then d119 (change p 160 (some 161)) else d7 (change p 160 (some 161))) = d120 p
  rw [sub4381, sub4380]
  rfl
theorem sub4383 (p : Pattern) : d121 (change p 160 (some 161)) = d121 p := by
  change (if p 204 then d12 (change p 160 (some 161)) else d120 (change p 160 (some 161))) = d121 p
  rw [sub4234, sub4382]
  rfl
theorem sub4384 (p : Pattern) : d148 (change p 160 (some 161)) = d148 p := by
  change (if p 182 then d121 (change p 160 (some 161)) else d120 (change p 160 (some 161))) = d148 p
  rw [sub4383, sub4382]
  rfl
theorem sub4385 (p : Pattern) : d153 (change p 160 (some 161)) = d153 p := by
  change (if p 163 then d12 (change p 160 (some 161)) else d148 (change p 160 (some 161))) = d153 p
  rw [sub4234, sub4384]
  rfl
theorem sub4386 (p : Pattern) : d154 (change p 160 (some 161)) = d154 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d153 (change p 160 (some 161))) = d154 p
  rw [sub4234, sub4385]
  rfl
theorem sub4387 (p : Pattern) : d246 (change p 160 (some 161)) = d154 p := by
  change d154 (change p 160 (some 161)) = d154 p
  exact sub4386 p
theorem sub4388 (p : Pattern) : d779 (change p 160 (some 161)) = d154 p := by
  change d246 (change p 160 (some 161)) = d154 p
  exact sub4387 p
theorem sub4389 (p : Pattern) : d780 (change p 160 (some 161)) = d4454 p := by
  change (if p 141 then d779 (change p 160 (some 161)) else d778 (change p 160 (some 161))) = d4454 p
  rw [sub4388, sub4379]
  rfl
theorem sub4390 (p : Pattern) : d781 (change p 160 (some 161)) = d4455 p := by
  change (if p 138 then d780 (change p 160 (some 161)) else d777 (change p 160 (some 161))) = d4455 p
  rw [sub4389, sub4377]
  rfl
theorem sub4391 (p : Pattern) : d254 (change p 160 (some 161)) = d254 p := by
  change (if p 163 then d26 (change p 160 (some 161)) else d109 (change p 160 (some 161))) = d254 p
  rw [sub4249, sub4312]
  rfl
theorem sub4392 (p : Pattern) : d255 (change p 160 (some 161)) = d255 p := by
  change (if p 162 then d12 (change p 160 (some 161)) else d254 (change p 160 (some 161))) = d255 p
  rw [sub4234, sub4391]
  rfl
theorem sub4393 (p : Pattern) : d256 (change p 160 (some 161)) = d255 p := by
  change d255 (change p 160 (some 161)) = d255 p
  exact sub4392 p
theorem sub4394 (p : Pattern) : d782 (change p 160 (some 161)) = d255 p := by
  change d256 (change p 160 (some 161)) = d255 p
  exact sub4393 p
theorem sub4395 (p : Pattern) : d783 (change p 160 (some 161)) = d4456 p := by
  change (if p 141 then d779 (change p 160 (some 161)) else d782 (change p 160 (some 161))) = d4456 p
  rw [sub4388, sub4394]
  rfl
theorem sub4396 (p : Pattern) : d784 (change p 160 (some 161)) = d4457 p := by
  change (if p 138 then d12 (change p 160 (some 161)) else d783 (change p 160 (some 161))) = d4457 p
  rw [sub4234, sub4395]
  rfl
theorem sub4397 (p : Pattern) : d785 (change p 160 (some 161)) = d4458 p := by
  change (if p 116 then d784 (change p 160 (some 161)) else d781 (change p 160 (some 161))) = d4458 p
  rw [sub4396, sub4390]
  rfl
theorem sub4398 (p : Pattern) : d786 (change p 160 (some 161)) = d4459 p := by
  change (if p 115 then d785 (change p 160 (some 161)) else d776 (change p 160 (some 161))) = d4459 p
  rw [sub4397, sub4376]
  rfl
theorem sub4399 (p : Pattern) : d787 (change p 160 (some 161)) = d4460 p := by
  change (if p 71 then d786 (change p 160 (some 161)) else d731 (change p 160 (some 161))) = d4460 p
  rw [sub4398, sub4292]
  rfl
theorem sub4400 (p : Pattern) : d788 (change p 160 (some 161)) = d4461 p := by
  change (if p 49 then d787 (change p 160 (some 161)) else d768 (change p 160 (some 161))) = d4461 p
  rw [sub4399, sub4365]
  rfl
theorem sub4401 (p : Pattern) : d789 (change p 160 (some 161)) = d4462 p := by
  change (if p 48 then d788 (change p 160 (some 161)) else d760 (change p 160 (some 161))) = d4462 p
  rw [sub4400, sub4341]
  rfl
theorem sub4402 (p : Pattern) : d0 (change p 138 (some 116)) = d0 p := by
  rfl
theorem sub4403 (p : Pattern) : d12 (change p 138 (some 116)) = d12 p := by
  rfl
theorem sub4404 (p : Pattern) : d13 (change p 138 (some 116)) = d13 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d0 (change p 138 (some 116))) = d13 p
  rw [sub4403, sub4402]
  rfl
theorem sub4405 (p : Pattern) : d14 (change p 138 (some 116)) = d14 p := by
  change (if p 246 then d13 (change p 138 (some 116)) else d0 (change p 138 (some 116))) = d14 p
  rw [sub4404, sub4402]
  rfl
theorem sub4406 (p : Pattern) : d15 (change p 138 (some 116)) = d15 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d14 (change p 138 (some 116))) = d15 p
  rw [sub4403, sub4405]
  rfl
theorem sub4407 (p : Pattern) : d16 (change p 138 (some 116)) = d16 p := by
  change (if p 182 then d15 (change p 138 (some 116)) else d14 (change p 138 (some 116))) = d16 p
  rw [sub4406, sub4405]
  rfl
theorem sub4408 (p : Pattern) : d4 (change p 138 (some 116)) = d4 p := by
  rfl
theorem sub4409 (p : Pattern) : d17 (change p 138 (some 116)) = d17 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d4 (change p 138 (some 116))) = d17 p
  rw [sub4403, sub4408]
  rfl
theorem sub4410 (p : Pattern) : d18 (change p 138 (some 116)) = d18 p := by
  change (if p 246 then d17 (change p 138 (some 116)) else d4 (change p 138 (some 116))) = d18 p
  rw [sub4409, sub4408]
  rfl
theorem sub4411 (p : Pattern) : d19 (change p 138 (some 116)) = d19 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d18 (change p 138 (some 116))) = d19 p
  rw [sub4403, sub4410]
  rfl
theorem sub4412 (p : Pattern) : d20 (change p 138 (some 116)) = d20 p := by
  change (if p 182 then d19 (change p 138 (some 116)) else d18 (change p 138 (some 116))) = d20 p
  rw [sub4411, sub4410]
  rfl
theorem sub4413 (p : Pattern) : d21 (change p 138 (some 116)) = d21 p := by
  change (if p 163 then d20 (change p 138 (some 116)) else d16 (change p 138 (some 116))) = d21 p
  rw [sub4412, sub4407]
  rfl
theorem sub4414 (p : Pattern) : d22 (change p 138 (some 116)) = d22 p := by
  change (if p 162 then d21 (change p 138 (some 116)) else d16 (change p 138 (some 116))) = d22 p
  rw [sub4413, sub4407]
  rfl
theorem sub4415 (p : Pattern) : d9 (change p 138 (some 116)) = d9 p := by
  rfl
theorem sub4416 (p : Pattern) : d23 (change p 138 (some 116)) = d23 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d9 (change p 138 (some 116))) = d23 p
  rw [sub4403, sub4415]
  rfl
theorem sub4417 (p : Pattern) : d24 (change p 138 (some 116)) = d24 p := by
  change (if p 246 then d23 (change p 138 (some 116)) else d9 (change p 138 (some 116))) = d24 p
  rw [sub4416, sub4415]
  rfl
theorem sub4418 (p : Pattern) : d25 (change p 138 (some 116)) = d25 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d24 (change p 138 (some 116))) = d25 p
  rw [sub4403, sub4417]
  rfl
theorem sub4419 (p : Pattern) : d26 (change p 138 (some 116)) = d26 p := by
  change (if p 182 then d25 (change p 138 (some 116)) else d24 (change p 138 (some 116))) = d26 p
  rw [sub4418, sub4417]
  rfl
theorem sub4420 (p : Pattern) : d27 (change p 138 (some 116)) = d27 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d26 (change p 138 (some 116))) = d27 p
  rw [sub4403, sub4419]
  rfl
theorem sub4421 (p : Pattern) : d28 (change p 138 (some 116)) = d28 p := by
  change (if p 162 then d27 (change p 138 (some 116)) else d21 (change p 138 (some 116))) = d28 p
  rw [sub4420, sub4413]
  rfl
theorem sub4422 (p : Pattern) : d29 (change p 138 (some 116)) = d29 p := by
  change (if p 161 then d28 (change p 138 (some 116)) else d22 (change p 138 (some 116))) = d29 p
  rw [sub4421, sub4414]
  rfl
theorem sub4423 (p : Pattern) : d518 (change p 138 (some 116)) = d518 p := by
  change (if p 204 then d18 (change p 138 (some 116)) else d14 (change p 138 (some 116))) = d518 p
  rw [sub4410, sub4405]
  rfl
theorem sub4424 (p : Pattern) : d6 (change p 138 (some 116)) = d6 p := by
  rfl
theorem sub4425 (p : Pattern) : d34 (change p 138 (some 116)) = d34 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d6 (change p 138 (some 116))) = d34 p
  rw [sub4403, sub4424]
  rfl
theorem sub4426 (p : Pattern) : d35 (change p 138 (some 116)) = d35 p := by
  change (if p 246 then d34 (change p 138 (some 116)) else d6 (change p 138 (some 116))) = d35 p
  rw [sub4425, sub4424]
  rfl
theorem sub4427 (p : Pattern) : d36 (change p 138 (some 116)) = d36 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d35 (change p 138 (some 116))) = d36 p
  rw [sub4403, sub4426]
  rfl
theorem sub4428 (p : Pattern) : d519 (change p 138 (some 116)) = d519 p := by
  change (if p 182 then d36 (change p 138 (some 116)) else d518 (change p 138 (some 116))) = d519 p
  rw [sub4427, sub4423]
  rfl
theorem sub4429 (p : Pattern) : d10 (change p 138 (some 116)) = d10 p := by
  rfl
theorem sub4430 (p : Pattern) : d57 (change p 138 (some 116)) = d57 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d10 (change p 138 (some 116))) = d57 p
  rw [sub4403, sub4429]
  rfl
theorem sub4431 (p : Pattern) : d58 (change p 138 (some 116)) = d58 p := by
  change (if p 246 then d57 (change p 138 (some 116)) else d10 (change p 138 (some 116))) = d58 p
  rw [sub4430, sub4429]
  rfl
theorem sub4432 (p : Pattern) : d59 (change p 138 (some 116)) = d59 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d58 (change p 138 (some 116))) = d59 p
  rw [sub4403, sub4431]
  rfl
theorem sub4433 (p : Pattern) : d520 (change p 138 (some 116)) = d520 p := by
  change (if p 182 then d59 (change p 138 (some 116)) else d518 (change p 138 (some 116))) = d520 p
  rw [sub4432, sub4423]
  rfl
theorem sub4434 (p : Pattern) : d521 (change p 138 (some 116)) = d521 p := by
  change (if p 163 then d520 (change p 138 (some 116)) else d519 (change p 138 (some 116))) = d521 p
  rw [sub4433, sub4428]
  rfl
theorem sub4435 (p : Pattern) : d522 (change p 138 (some 116)) = d522 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d518 (change p 138 (some 116))) = d522 p
  rw [sub4403, sub4423]
  rfl
theorem sub4436 (p : Pattern) : d8 (change p 138 (some 116)) = d8 p := by
  rfl
theorem sub4437 (p : Pattern) : d190 (change p 138 (some 116)) = d190 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d8 (change p 138 (some 116))) = d190 p
  rw [sub4403, sub4436]
  rfl
theorem sub4438 (p : Pattern) : d191 (change p 138 (some 116)) = d191 p := by
  change (if p 246 then d190 (change p 138 (some 116)) else d8 (change p 138 (some 116))) = d191 p
  rw [sub4437, sub4436]
  rfl
theorem sub4439 (p : Pattern) : d523 (change p 138 (some 116)) = d523 p := by
  change (if p 204 then d191 (change p 138 (some 116)) else d18 (change p 138 (some 116))) = d523 p
  rw [sub4438, sub4410]
  rfl
end NetHack.Sokoban22Refined85
