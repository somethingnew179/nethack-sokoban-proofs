/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions37
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4560 (p : Pattern) : d594 (change p 138 (some 116)) = d594 p := by
  change (if p 162 then d539 (change p 138 (some 116)) else d592 (change p 138 (some 116))) = d594 p
  rw [sub4474, sub4558]
  rfl
theorem sub4561 (p : Pattern) : d595 (change p 138 (some 116)) = d595 p := by
  change (if p 161 then d594 (change p 138 (some 116)) else d593 (change p 138 (some 116))) = d595 p
  rw [sub4560, sub4559]
  rfl
theorem sub4562 (p : Pattern) : d596 (change p 138 (some 116)) = d596 p := by
  change (if p 160 then d595 (change p 138 (some 116)) else d189 (change p 138 (some 116))) = d596 p
  rw [sub4561, sub4553]
  rfl
theorem sub4563 (p : Pattern) : d198 (change p 138 (some 116)) = d198 p := by
  change (if p 163 then d62 (change p 138 (some 116)) else d20 (change p 138 (some 116))) = d198 p
  rw [sub4462, sub4412]
  rfl
theorem sub4564 (p : Pattern) : d199 (change p 138 (some 116)) = d199 p := by
  change (if p 162 then d198 (change p 138 (some 116)) else d53 (change p 138 (some 116))) = d199 p
  rw [sub4563, sub4452]
  rfl
theorem sub4565 (p : Pattern) : d83 (change p 138 (some 116)) = d83 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d78 (change p 138 (some 116))) = d83 p
  rw [sub4403, sub4549]
  rfl
theorem sub4566 (p : Pattern) : d84 (change p 138 (some 116)) = d84 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d83 (change p 138 (some 116))) = d84 p
  rw [sub4403, sub4565]
  rfl
theorem sub4567 (p : Pattern) : d200 (change p 138 (some 116)) = d200 p := by
  change (if p 161 then d84 (change p 138 (some 116)) else d199 (change p 138 (some 116))) = d200 p
  rw [sub4566, sub4564]
  rfl
theorem sub4568 (p : Pattern) : d597 (change p 138 (some 116)) = d597 p := by
  change (if p 182 then d59 (change p 138 (some 116)) else d588 (change p 138 (some 116))) = d597 p
  rw [sub4432, sub4554]
  rfl
theorem sub4569 (p : Pattern) : d598 (change p 138 (some 116)) = d598 p := by
  change (if p 163 then d533 (change p 138 (some 116)) else d597 (change p 138 (some 116))) = d598 p
  rw [sub4467, sub4568]
  rfl
theorem sub4570 (p : Pattern) : d599 (change p 138 (some 116)) = d599 p := by
  change (if p 163 then d538 (change p 138 (some 116)) else d524 (change p 138 (some 116))) = d599 p
  rw [sub4473, sub4440]
  rfl
theorem sub4571 (p : Pattern) : d600 (change p 138 (some 116)) = d600 p := by
  change (if p 162 then d599 (change p 138 (some 116)) else d598 (change p 138 (some 116))) = d600 p
  rw [sub4570, sub4569]
  rfl
theorem sub4572 (p : Pattern) : d601 (change p 138 (some 116)) = d601 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d591 (change p 138 (some 116))) = d601 p
  rw [sub4403, sub4557]
  rfl
theorem sub4573 (p : Pattern) : d602 (change p 138 (some 116)) = d602 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d601 (change p 138 (some 116))) = d602 p
  rw [sub4403, sub4572]
  rfl
theorem sub4574 (p : Pattern) : d603 (change p 138 (some 116)) = d603 p := by
  change (if p 161 then d602 (change p 138 (some 116)) else d600 (change p 138 (some 116))) = d603 p
  rw [sub4573, sub4571]
  rfl
theorem sub4575 (p : Pattern) : d604 (change p 138 (some 116)) = d604 p := by
  change (if p 160 then d603 (change p 138 (some 116)) else d200 (change p 138 (some 116))) = d604 p
  rw [sub4574, sub4567]
  rfl
theorem sub4576 (p : Pattern) : d605 (change p 138 (some 116)) = d605 p := by
  change (if p 141 then d604 (change p 138 (some 116)) else d596 (change p 138 (some 116))) = d605 p
  rw [sub4575, sub4562]
  rfl
theorem sub4577 (p : Pattern) : d606 (change p 138 (some 116)) = d605 p := by
  change d605 (change p 138 (some 116)) = d605 p
  exact sub4576 p
theorem sub4578 (p : Pattern) : d607 (change p 138 (some 116)) = d605 p := by
  change d606 (change p 138 (some 116)) = d605 p
  exact sub4577 p
theorem sub4579 (p : Pattern) : d608 (change p 138 (some 116)) = d4465 p := by
  change (if p 115 then d607 (change p 138 (some 116)) else d552 (change p 138 (some 116))) = d4465 p
  rw [sub4578, sub4485]
  rfl
theorem sub4580 (p : Pattern) : d609 (change p 138 (some 116)) = d4466 p := by
  change (if p 71 then d608 (change p 138 (some 116)) else d549 (change p 138 (some 116))) = d4466 p
  rw [sub4579, sub4483]
  rfl
theorem sub4581 (p : Pattern) : d211 (change p 138 (some 116)) = d211 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d109 (change p 138 (some 116))) = d211 p
  rw [sub4403, sub4498]
  rfl
theorem sub4582 (p : Pattern) : d212 (change p 138 (some 116)) = d212 p := by
  change (if p 162 then d211 (change p 138 (some 116)) else d133 (change p 138 (some 116))) = d212 p
  rw [sub4581, sub4526]
  rfl
theorem sub4583 (p : Pattern) : d213 (change p 138 (some 116)) = d213 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d211 (change p 138 (some 116))) = d213 p
  rw [sub4403, sub4581]
  rfl
theorem sub4584 (p : Pattern) : d214 (change p 138 (some 116)) = d214 p := by
  change (if p 161 then d213 (change p 138 (some 116)) else d212 (change p 138 (some 116))) = d214 p
  rw [sub4583, sub4582]
  rfl
theorem sub4585 (p : Pattern) : d611 (change p 138 (some 116)) = d611 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d564 (change p 138 (some 116))) = d611 p
  rw [sub4403, sub4514]
  rfl
theorem sub4586 (p : Pattern) : d612 (change p 138 (some 116)) = d612 p := by
  change (if p 162 then d611 (change p 138 (some 116)) else d572 (change p 138 (some 116))) = d612 p
  rw [sub4585, sub4534]
  rfl
theorem sub4587 (p : Pattern) : d613 (change p 138 (some 116)) = d613 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d611 (change p 138 (some 116))) = d613 p
  rw [sub4403, sub4585]
  rfl
theorem sub4588 (p : Pattern) : d614 (change p 138 (some 116)) = d614 p := by
  change (if p 161 then d613 (change p 138 (some 116)) else d612 (change p 138 (some 116))) = d614 p
  rw [sub4587, sub4586]
  rfl
theorem sub4589 (p : Pattern) : d615 (change p 138 (some 116)) = d615 p := by
  change (if p 160 then d614 (change p 138 (some 116)) else d214 (change p 138 (some 116))) = d615 p
  rw [sub4588, sub4584]
  rfl
theorem sub4590 (p : Pattern) : d616 (change p 138 (some 116)) = d616 p := by
  change (if p 141 then d615 (change p 138 (some 116)) else d569 (change p 138 (some 116))) = d616 p
  rw [sub4589, sub4520]
  rfl
theorem sub4591 (p : Pattern) : d617 (change p 138 (some 116)) = d616 p := by
  change d616 (change p 138 (some 116)) = d616 p
  exact sub4590 p
theorem sub4592 (p : Pattern) : d618 (change p 138 (some 116)) = d616 p := by
  change d617 (change p 138 (some 116)) = d616 p
  exact sub4591 p
theorem sub4593 (p : Pattern) : d252 (change p 138 (some 116)) = d252 p := by
  change (if p 163 then d26 (change p 138 (some 116)) else d132 (change p 138 (some 116))) = d252 p
  rw [sub4419, sub4525]
  rfl
theorem sub4594 (p : Pattern) : d253 (change p 138 (some 116)) = d253 p := by
  change (if p 162 then d252 (change p 138 (some 116)) else d105 (change p 138 (some 116))) = d253 p
  rw [sub4593, sub4493]
  rfl
theorem sub4595 (p : Pattern) : d254 (change p 138 (some 116)) = d254 p := by
  change (if p 163 then d26 (change p 138 (some 116)) else d109 (change p 138 (some 116))) = d254 p
  rw [sub4419, sub4498]
  rfl
theorem sub4596 (p : Pattern) : d255 (change p 138 (some 116)) = d255 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d254 (change p 138 (some 116))) = d255 p
  rw [sub4403, sub4595]
  rfl
theorem sub4597 (p : Pattern) : d256 (change p 138 (some 116)) = d256 p := by
  change (if p 161 then d255 (change p 138 (some 116)) else d253 (change p 138 (some 116))) = d256 p
  rw [sub4596, sub4594]
  rfl
theorem sub4598 (p : Pattern) : d620 (change p 138 (some 116)) = d620 p := by
  change (if p 204 then d120 (change p 138 (some 116)) else d103 (change p 138 (some 116))) = d620 p
  rw [sub4507, sub4491]
  rfl
theorem sub4599 (p : Pattern) : d621 (change p 138 (some 116)) = d621 p := by
  change (if p 182 then d121 (change p 138 (some 116)) else d620 (change p 138 (some 116))) = d621 p
  rw [sub4508, sub4598]
  rfl
theorem sub4600 (p : Pattern) : d622 (change p 138 (some 116)) = d622 p := by
  change (if p 182 then d41 (change p 138 (some 116)) else d620 (change p 138 (some 116))) = d622 p
  rw [sub4461, sub4598]
  rfl
theorem sub4601 (p : Pattern) : d623 (change p 138 (some 116)) = d623 p := by
  change (if p 163 then d622 (change p 138 (some 116)) else d621 (change p 138 (some 116))) = d623 p
  rw [sub4600, sub4599]
  rfl
theorem sub4602 (p : Pattern) : d624 (change p 138 (some 116)) = d624 p := by
  change (if p 204 then d40 (change p 138 (some 116)) else d24 (change p 138 (some 116))) = d624 p
  rw [sub4460, sub4417]
  rfl
theorem sub4603 (p : Pattern) : d625 (change p 138 (some 116)) = d625 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d624 (change p 138 (some 116))) = d625 p
  rw [sub4403, sub4602]
  rfl
theorem sub4604 (p : Pattern) : d626 (change p 138 (some 116)) = d626 p := by
  change (if p 163 then d625 (change p 138 (some 116)) else d571 (change p 138 (some 116))) = d626 p
  rw [sub4603, sub4533]
  rfl
theorem sub4605 (p : Pattern) : d627 (change p 138 (some 116)) = d627 p := by
  change (if p 162 then d626 (change p 138 (some 116)) else d623 (change p 138 (some 116))) = d627 p
  rw [sub4604, sub4601]
  rfl
theorem sub4606 (p : Pattern) : d273 (change p 138 (some 116)) = d273 p := by
  change (if p 204 then d120 (change p 138 (some 116)) else d107 (change p 138 (some 116))) = d273 p
  rw [sub4507, sub4496]
  rfl
theorem sub4607 (p : Pattern) : d274 (change p 138 (some 116)) = d274 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d273 (change p 138 (some 116))) = d274 p
  rw [sub4403, sub4606]
  rfl
theorem sub4608 (p : Pattern) : d628 (change p 138 (some 116)) = d628 p := by
  change (if p 163 then d625 (change p 138 (some 116)) else d274 (change p 138 (some 116))) = d628 p
  rw [sub4603, sub4607]
  rfl
theorem sub4609 (p : Pattern) : d629 (change p 138 (some 116)) = d629 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d628 (change p 138 (some 116))) = d629 p
  rw [sub4403, sub4608]
  rfl
theorem sub4610 (p : Pattern) : d630 (change p 138 (some 116)) = d630 p := by
  change (if p 161 then d629 (change p 138 (some 116)) else d627 (change p 138 (some 116))) = d630 p
  rw [sub4609, sub4605]
  rfl
theorem sub4611 (p : Pattern) : d631 (change p 138 (some 116)) = d631 p := by
  change (if p 160 then d630 (change p 138 (some 116)) else d256 (change p 138 (some 116))) = d631 p
  rw [sub4610, sub4597]
  rfl
theorem sub4612 (p : Pattern) : d245 (change p 138 (some 116)) = d245 p := by
  change (if p 162 then d211 (change p 138 (some 116)) else d132 (change p 138 (some 116))) = d245 p
  rw [sub4581, sub4525]
  rfl
theorem sub4613 (p : Pattern) : d148 (change p 138 (some 116)) = d148 p := by
  change (if p 182 then d121 (change p 138 (some 116)) else d120 (change p 138 (some 116))) = d148 p
  rw [sub4508, sub4507]
  rfl
theorem sub4614 (p : Pattern) : d153 (change p 138 (some 116)) = d153 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d148 (change p 138 (some 116))) = d153 p
  rw [sub4403, sub4613]
  rfl
theorem sub4615 (p : Pattern) : d154 (change p 138 (some 116)) = d154 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d153 (change p 138 (some 116))) = d154 p
  rw [sub4403, sub4614]
  rfl
theorem sub4616 (p : Pattern) : d246 (change p 138 (some 116)) = d246 p := by
  change (if p 161 then d154 (change p 138 (some 116)) else d245 (change p 138 (some 116))) = d246 p
  rw [sub4615, sub4612]
  rfl
theorem sub4617 (p : Pattern) : d632 (change p 138 (some 116)) = d632 p := by
  change (if p 182 then d41 (change p 138 (some 116)) else d570 (change p 138 (some 116))) = d632 p
  rw [sub4461, sub4532]
  rfl
theorem sub4618 (p : Pattern) : d633 (change p 138 (some 116)) = d633 p := by
  change (if p 204 then d24 (change p 138 (some 116)) else d116 (change p 138 (some 116))) = d633 p
  rw [sub4417, sub4523]
  rfl
theorem sub4619 (p : Pattern) : d634 (change p 138 (some 116)) = d634 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d633 (change p 138 (some 116))) = d634 p
  rw [sub4403, sub4618]
  rfl
theorem sub4620 (p : Pattern) : d635 (change p 138 (some 116)) = d635 p := by
  change (if p 163 then d634 (change p 138 (some 116)) else d632 (change p 138 (some 116))) = d635 p
  rw [sub4619, sub4617]
  rfl
theorem sub4621 (p : Pattern) : d636 (change p 138 (some 116)) = d636 p := by
  change (if p 204 then d40 (change p 138 (some 116)) else d107 (change p 138 (some 116))) = d636 p
  rw [sub4460, sub4496]
  rfl
theorem sub4622 (p : Pattern) : d637 (change p 138 (some 116)) = d637 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d636 (change p 138 (some 116))) = d637 p
  rw [sub4403, sub4621]
  rfl
theorem sub4623 (p : Pattern) : d638 (change p 138 (some 116)) = d638 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d637 (change p 138 (some 116))) = d638 p
  rw [sub4403, sub4622]
  rfl
theorem sub4624 (p : Pattern) : d639 (change p 138 (some 116)) = d639 p := by
  change (if p 162 then d638 (change p 138 (some 116)) else d635 (change p 138 (some 116))) = d639 p
  rw [sub4623, sub4620]
  rfl
theorem sub4625 (p : Pattern) : d640 (change p 138 (some 116)) = d640 p := by
  change (if p 204 then d40 (change p 138 (some 116)) else d120 (change p 138 (some 116))) = d640 p
  rw [sub4460, sub4507]
  rfl
theorem sub4626 (p : Pattern) : d641 (change p 138 (some 116)) = d641 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d640 (change p 138 (some 116))) = d641 p
  rw [sub4403, sub4625]
  rfl
theorem sub4627 (p : Pattern) : d642 (change p 138 (some 116)) = d642 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d641 (change p 138 (some 116))) = d642 p
  rw [sub4403, sub4626]
  rfl
theorem sub4628 (p : Pattern) : d643 (change p 138 (some 116)) = d643 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d642 (change p 138 (some 116))) = d643 p
  rw [sub4403, sub4627]
  rfl
theorem sub4629 (p : Pattern) : d644 (change p 138 (some 116)) = d644 p := by
  change (if p 161 then d643 (change p 138 (some 116)) else d639 (change p 138 (some 116))) = d644 p
  rw [sub4628, sub4624]
  rfl
theorem sub4630 (p : Pattern) : d645 (change p 138 (some 116)) = d645 p := by
  change (if p 160 then d644 (change p 138 (some 116)) else d246 (change p 138 (some 116))) = d645 p
  rw [sub4629, sub4616]
  rfl
theorem sub4631 (p : Pattern) : d646 (change p 138 (some 116)) = d646 p := by
  change (if p 141 then d645 (change p 138 (some 116)) else d631 (change p 138 (some 116))) = d646 p
  rw [sub4630, sub4611]
  rfl
theorem sub4632 (p : Pattern) : d647 (change p 138 (some 116)) = d646 p := by
  change d646 (change p 138 (some 116)) = d646 p
  exact sub4631 p
theorem sub4633 (p : Pattern) : d648 (change p 138 (some 116)) = d646 p := by
  change d647 (change p 138 (some 116)) = d646 p
  exact sub4632 p
theorem sub4634 (p : Pattern) : d649 (change p 138 (some 116)) = d4467 p := by
  change (if p 115 then d648 (change p 138 (some 116)) else d618 (change p 138 (some 116))) = d4467 p
  rw [sub4633, sub4592]
  rfl
theorem sub4635 (p : Pattern) : d650 (change p 138 (some 116)) = d4468 p := by
  change (if p 71 then d649 (change p 138 (some 116)) else d549 (change p 138 (some 116))) = d4468 p
  rw [sub4634, sub4483]
  rfl
theorem sub4636 (p : Pattern) : d651 (change p 138 (some 116)) = d4469 p := by
  change (if p 49 then d650 (change p 138 (some 116)) else d609 (change p 138 (some 116))) = d4469 p
  rw [sub4635, sub4580]
  rfl
theorem sub4637 (p : Pattern) : d652 (change p 138 (some 116)) = d4470 p := by
  change (if p 48 then d651 (change p 138 (some 116)) else d587 (change p 138 (some 116))) = d4470 p
  rw [sub4636, sub4548]
  rfl
theorem sub4638 (p : Pattern) : d0 (change p 182 (some 204)) = d0 p := by
  rfl
theorem sub4639 (p : Pattern) : d12 (change p 182 (some 204)) = d12 p := by
  rfl
theorem sub4640 (p : Pattern) : d13 (change p 182 (some 204)) = d13 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d0 (change p 182 (some 204))) = d13 p
  rw [sub4639, sub4638]
  rfl
theorem sub4641 (p : Pattern) : d14 (change p 182 (some 204)) = d14 p := by
  change (if p 246 then d13 (change p 182 (some 204)) else d0 (change p 182 (some 204))) = d14 p
  rw [sub4640, sub4638]
  rfl
theorem sub4642 (p : Pattern) : d1504 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4643 (p : Pattern) : d1505 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4644 (p : Pattern) : d1506 (change p 182 (some 204)) = d14 p := by
  change (if p 163 then d1505 (change p 182 (some 204)) else d1504 (change p 182 (some 204))) = d14 p
  rw [sub4643, sub4642]
  simp only [ite_self]
theorem sub4645 (p : Pattern) : d1507 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4646 (p : Pattern) : d4 (change p 182 (some 204)) = d4 p := by
  rfl
theorem sub4647 (p : Pattern) : d17 (change p 182 (some 204)) = d17 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d4 (change p 182 (some 204))) = d17 p
  rw [sub4639, sub4646]
  rfl
theorem sub4648 (p : Pattern) : d18 (change p 182 (some 204)) = d18 p := by
  change (if p 246 then d17 (change p 182 (some 204)) else d4 (change p 182 (some 204))) = d18 p
  rw [sub4647, sub4646]
  rfl
theorem sub4649 (p : Pattern) : d43 (change p 182 (some 204)) = d18 p := by
  change d18 (change p 182 (some 204)) = d18 p
  exact sub4648 p
theorem sub4650 (p : Pattern) : d1508 (change p 182 (some 204)) = d4477 p := by
  change (if p 163 then d43 (change p 182 (some 204)) else d1507 (change p 182 (some 204))) = d4477 p
  rw [sub4649, sub4645]
  rfl
theorem sub4651 (p : Pattern) : d1509 (change p 182 (some 204)) = d4478 p := by
  change (if p 162 then d1508 (change p 182 (some 204)) else d1506 (change p 182 (some 204))) = d4478 p
  rw [sub4650, sub4644]
  rfl
theorem sub4652 (p : Pattern) : d46 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4653 (p : Pattern) : d47 (change p 182 (some 204)) = d4477 p := by
  change (if p 163 then d43 (change p 182 (some 204)) else d46 (change p 182 (some 204))) = d4477 p
  rw [sub4649, sub4652]
  rfl
theorem sub4654 (p : Pattern) : d9 (change p 182 (some 204)) = d9 p := by
  rfl
theorem sub4655 (p : Pattern) : d23 (change p 182 (some 204)) = d23 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d9 (change p 182 (some 204))) = d23 p
  rw [sub4639, sub4654]
  rfl
theorem sub4656 (p : Pattern) : d24 (change p 182 (some 204)) = d24 p := by
  change (if p 246 then d23 (change p 182 (some 204)) else d9 (change p 182 (some 204))) = d24 p
  rw [sub4655, sub4654]
  rfl
theorem sub4657 (p : Pattern) : d48 (change p 182 (some 204)) = d24 p := by
  change d24 (change p 182 (some 204)) = d24 p
  exact sub4656 p
theorem sub4658 (p : Pattern) : d49 (change p 182 (some 204)) = d4479 p := by
  change (if p 163 then d12 (change p 182 (some 204)) else d48 (change p 182 (some 204))) = d4479 p
  rw [sub4639, sub4657]
  rfl
theorem sub4659 (p : Pattern) : d50 (change p 182 (some 204)) = d4480 p := by
  change (if p 162 then d49 (change p 182 (some 204)) else d47 (change p 182 (some 204))) = d4480 p
  rw [sub4658, sub4653]
  rfl
theorem sub4660 (p : Pattern) : d1510 (change p 182 (some 204)) = d4481 p := by
  change (if p 161 then d50 (change p 182 (some 204)) else d1509 (change p 182 (some 204))) = d4481 p
  rw [sub4659, sub4651]
  rfl
theorem sub4661 (p : Pattern) : d1511 (change p 182 (some 204)) = d4478 p := by
  change (if p 162 then d47 (change p 182 (some 204)) else d46 (change p 182 (some 204))) = d4478 p
  rw [sub4653, sub4652]
  rfl
theorem sub4662 (p : Pattern) : d1512 (change p 182 (some 204)) = d4481 p := by
  change (if p 161 then d50 (change p 182 (some 204)) else d1511 (change p 182 (some 204))) = d4481 p
  rw [sub4659, sub4661]
  rfl
theorem sub4663 (p : Pattern) : d1513 (change p 182 (some 204)) = d4481 p := by
  change (if p 160 then d1512 (change p 182 (some 204)) else d1510 (change p 182 (some 204))) = d4481 p
  rw [sub4662, sub4660]
  simp only [ite_self]
theorem sub4664 (p : Pattern) : d1514 (change p 182 (some 204)) = d14 p := by
  change d14 (change p 182 (some 204)) = d14 p
  exact sub4641 p
theorem sub4665 (p : Pattern) : d2 (change p 182 (some 204)) = d2 p := by
  rfl
theorem sub4666 (p : Pattern) : d30 (change p 182 (some 204)) = d30 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d2 (change p 182 (some 204))) = d30 p
  rw [sub4639, sub4665]
  rfl
theorem sub4667 (p : Pattern) : d31 (change p 182 (some 204)) = d31 p := by
  change (if p 246 then d30 (change p 182 (some 204)) else d2 (change p 182 (some 204))) = d31 p
  rw [sub4666, sub4665]
  rfl
theorem sub4668 (p : Pattern) : d66 (change p 182 (some 204)) = d31 p := by
  change d31 (change p 182 (some 204)) = d31 p
  exact sub4667 p
theorem sub4669 (p : Pattern) : d1515 (change p 182 (some 204)) = d4482 p := by
  change (if p 163 then d66 (change p 182 (some 204)) else d1514 (change p 182 (some 204))) = d4482 p
  rw [sub4668, sub4664]
  rfl
theorem sub4670 (p : Pattern) : d68 (change p 182 (some 204)) = d4483 p := by
  change (if p 163 then d48 (change p 182 (some 204)) else d43 (change p 182 (some 204))) = d4483 p
  rw [sub4657, sub4649]
  rfl
theorem sub4671 (p : Pattern) : d1516 (change p 182 (some 204)) = d4484 p := by
  change (if p 162 then d68 (change p 182 (some 204)) else d1515 (change p 182 (some 204))) = d4484 p
  rw [sub4670, sub4669]
  rfl
theorem sub4672 (p : Pattern) : d10 (change p 182 (some 204)) = d10 p := by
  rfl
theorem sub4673 (p : Pattern) : d57 (change p 182 (some 204)) = d57 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d10 (change p 182 (some 204))) = d57 p
  rw [sub4639, sub4672]
  rfl
theorem sub4674 (p : Pattern) : d58 (change p 182 (some 204)) = d58 p := by
  change (if p 246 then d57 (change p 182 (some 204)) else d10 (change p 182 (some 204))) = d58 p
  rw [sub4673, sub4672]
  rfl
theorem sub4675 (p : Pattern) : d70 (change p 182 (some 204)) = d58 p := by
  change d58 (change p 182 (some 204)) = d58 p
  exact sub4674 p
theorem sub4676 (p : Pattern) : d71 (change p 182 (some 204)) = d4485 p := by
  change (if p 163 then d70 (change p 182 (some 204)) else d43 (change p 182 (some 204))) = d4485 p
  rw [sub4675, sub4649]
  rfl
theorem sub4677 (p : Pattern) : d11 (change p 182 (some 204)) = d11 p := by
  rfl
theorem sub4678 (p : Pattern) : d39 (change p 182 (some 204)) = d39 p := by
  change (if p 247 then d12 (change p 182 (some 204)) else d11 (change p 182 (some 204))) = d39 p
  rw [sub4639, sub4677]
  rfl
theorem sub4679 (p : Pattern) : d40 (change p 182 (some 204)) = d40 p := by
  change (if p 246 then d39 (change p 182 (some 204)) else d11 (change p 182 (some 204))) = d40 p
  rw [sub4678, sub4677]
  rfl
end NetHack.Sokoban22Refined85
