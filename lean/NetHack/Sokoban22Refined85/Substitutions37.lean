/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions36
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4440 (p : Pattern) : d524 (change p 138 (some 116)) = d524 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d523 (change p 138 (some 116))) = d524 p
  rw [sub4403, sub4439]
  rfl
theorem sub4441 (p : Pattern) : d525 (change p 138 (some 116)) = d525 p := by
  change (if p 163 then d524 (change p 138 (some 116)) else d522 (change p 138 (some 116))) = d525 p
  rw [sub4440, sub4435]
  rfl
theorem sub4442 (p : Pattern) : d526 (change p 138 (some 116)) = d526 p := by
  change (if p 162 then d525 (change p 138 (some 116)) else d521 (change p 138 (some 116))) = d526 p
  rw [sub4441, sub4434]
  rfl
theorem sub4443 (p : Pattern) : d527 (change p 138 (some 116)) = d527 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d25 (change p 138 (some 116))) = d527 p
  rw [sub4403, sub4418]
  rfl
theorem sub4444 (p : Pattern) : d528 (change p 138 (some 116)) = d528 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d527 (change p 138 (some 116))) = d528 p
  rw [sub4403, sub4443]
  rfl
theorem sub4445 (p : Pattern) : d529 (change p 138 (some 116)) = d529 p := by
  change (if p 162 then d528 (change p 138 (some 116)) else d525 (change p 138 (some 116))) = d529 p
  rw [sub4444, sub4441]
  rfl
theorem sub4446 (p : Pattern) : d530 (change p 138 (some 116)) = d530 p := by
  change (if p 161 then d529 (change p 138 (some 116)) else d526 (change p 138 (some 116))) = d530 p
  rw [sub4445, sub4442]
  rfl
theorem sub4447 (p : Pattern) : d531 (change p 138 (some 116)) = d531 p := by
  change (if p 160 then d530 (change p 138 (some 116)) else d29 (change p 138 (some 116))) = d531 p
  rw [sub4446, sub4422]
  rfl
theorem sub4448 (p : Pattern) : d2 (change p 138 (some 116)) = d2 p := by
  rfl
theorem sub4449 (p : Pattern) : d30 (change p 138 (some 116)) = d30 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d2 (change p 138 (some 116))) = d30 p
  rw [sub4403, sub4448]
  rfl
theorem sub4450 (p : Pattern) : d31 (change p 138 (some 116)) = d31 p := by
  change (if p 246 then d30 (change p 138 (some 116)) else d2 (change p 138 (some 116))) = d31 p
  rw [sub4449, sub4448]
  rfl
theorem sub4451 (p : Pattern) : d32 (change p 138 (some 116)) = d32 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d31 (change p 138 (some 116))) = d32 p
  rw [sub4403, sub4450]
  rfl
theorem sub4452 (p : Pattern) : d53 (change p 138 (some 116)) = d53 p := by
  change (if p 182 then d32 (change p 138 (some 116)) else d31 (change p 138 (some 116))) = d53 p
  rw [sub4451, sub4450]
  rfl
theorem sub4453 (p : Pattern) : d54 (change p 138 (some 116)) = d54 p := by
  change (if p 163 then d53 (change p 138 (some 116)) else d16 (change p 138 (some 116))) = d54 p
  rw [sub4452, sub4407]
  rfl
theorem sub4454 (p : Pattern) : d55 (change p 138 (some 116)) = d55 p := by
  change (if p 163 then d26 (change p 138 (some 116)) else d20 (change p 138 (some 116))) = d55 p
  rw [sub4419, sub4412]
  rfl
theorem sub4455 (p : Pattern) : d56 (change p 138 (some 116)) = d56 p := by
  change (if p 162 then d55 (change p 138 (some 116)) else d54 (change p 138 (some 116))) = d56 p
  rw [sub4454, sub4453]
  rfl
theorem sub4456 (p : Pattern) : d60 (change p 138 (some 116)) = d60 p := by
  change (if p 182 then d59 (change p 138 (some 116)) else d58 (change p 138 (some 116))) = d60 p
  rw [sub4432, sub4431]
  rfl
theorem sub4457 (p : Pattern) : d61 (change p 138 (some 116)) = d61 p := by
  change (if p 163 then d60 (change p 138 (some 116)) else d20 (change p 138 (some 116))) = d61 p
  rw [sub4456, sub4412]
  rfl
theorem sub4458 (p : Pattern) : d11 (change p 138 (some 116)) = d11 p := by
  rfl
theorem sub4459 (p : Pattern) : d39 (change p 138 (some 116)) = d39 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d11 (change p 138 (some 116))) = d39 p
  rw [sub4403, sub4458]
  rfl
theorem sub4460 (p : Pattern) : d40 (change p 138 (some 116)) = d40 p := by
  change (if p 246 then d39 (change p 138 (some 116)) else d11 (change p 138 (some 116))) = d40 p
  rw [sub4459, sub4458]
  rfl
theorem sub4461 (p : Pattern) : d41 (change p 138 (some 116)) = d41 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d40 (change p 138 (some 116))) = d41 p
  rw [sub4403, sub4460]
  rfl
theorem sub4462 (p : Pattern) : d62 (change p 138 (some 116)) = d62 p := by
  change (if p 182 then d41 (change p 138 (some 116)) else d40 (change p 138 (some 116))) = d62 p
  rw [sub4461, sub4460]
  rfl
theorem sub4463 (p : Pattern) : d63 (change p 138 (some 116)) = d63 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d62 (change p 138 (some 116))) = d63 p
  rw [sub4403, sub4462]
  rfl
theorem sub4464 (p : Pattern) : d64 (change p 138 (some 116)) = d64 p := by
  change (if p 162 then d63 (change p 138 (some 116)) else d61 (change p 138 (some 116))) = d64 p
  rw [sub4463, sub4457]
  rfl
theorem sub4465 (p : Pattern) : d65 (change p 138 (some 116)) = d65 p := by
  change (if p 161 then d64 (change p 138 (some 116)) else d56 (change p 138 (some 116))) = d65 p
  rw [sub4464, sub4455]
  rfl
theorem sub4466 (p : Pattern) : d532 (change p 138 (some 116)) = d532 p := by
  change (if p 204 then d35 (change p 138 (some 116)) else d31 (change p 138 (some 116))) = d532 p
  rw [sub4426, sub4450]
  rfl
theorem sub4467 (p : Pattern) : d533 (change p 138 (some 116)) = d533 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d532 (change p 138 (some 116))) = d533 p
  rw [sub4403, sub4466]
  rfl
theorem sub4468 (p : Pattern) : d534 (change p 138 (some 116)) = d534 p := by
  change (if p 163 then d533 (change p 138 (some 116)) else d520 (change p 138 (some 116))) = d534 p
  rw [sub4467, sub4433]
  rfl
theorem sub4469 (p : Pattern) : d535 (change p 138 (some 116)) = d535 p := by
  change (if p 163 then d527 (change p 138 (some 116)) else d524 (change p 138 (some 116))) = d535 p
  rw [sub4443, sub4440]
  rfl
theorem sub4470 (p : Pattern) : d536 (change p 138 (some 116)) = d536 p := by
  change (if p 162 then d535 (change p 138 (some 116)) else d534 (change p 138 (some 116))) = d536 p
  rw [sub4469, sub4468]
  rfl
theorem sub4471 (p : Pattern) : d277 (change p 138 (some 116)) = d277 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d59 (change p 138 (some 116))) = d277 p
  rw [sub4403, sub4432]
  rfl
theorem sub4472 (p : Pattern) : d537 (change p 138 (some 116)) = d537 p := by
  change (if p 163 then d277 (change p 138 (some 116)) else d524 (change p 138 (some 116))) = d537 p
  rw [sub4471, sub4440]
  rfl
theorem sub4473 (p : Pattern) : d538 (change p 138 (some 116)) = d538 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d41 (change p 138 (some 116))) = d538 p
  rw [sub4403, sub4461]
  rfl
theorem sub4474 (p : Pattern) : d539 (change p 138 (some 116)) = d539 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d538 (change p 138 (some 116))) = d539 p
  rw [sub4403, sub4473]
  rfl
theorem sub4475 (p : Pattern) : d540 (change p 138 (some 116)) = d540 p := by
  change (if p 162 then d539 (change p 138 (some 116)) else d537 (change p 138 (some 116))) = d540 p
  rw [sub4474, sub4472]
  rfl
theorem sub4476 (p : Pattern) : d541 (change p 138 (some 116)) = d541 p := by
  change (if p 161 then d540 (change p 138 (some 116)) else d536 (change p 138 (some 116))) = d541 p
  rw [sub4475, sub4470]
  rfl
theorem sub4477 (p : Pattern) : d542 (change p 138 (some 116)) = d542 p := by
  change (if p 160 then d541 (change p 138 (some 116)) else d65 (change p 138 (some 116))) = d542 p
  rw [sub4476, sub4465]
  rfl
theorem sub4478 (p : Pattern) : d543 (change p 138 (some 116)) = d543 p := by
  change (if p 141 then d542 (change p 138 (some 116)) else d531 (change p 138 (some 116))) = d543 p
  rw [sub4477, sub4447]
  rfl
theorem sub4479 (p : Pattern) : d544 (change p 138 (some 116)) = d543 p := by
  change d543 (change p 138 (some 116)) = d543 p
  exact sub4478 p
theorem sub4480 (p : Pattern) : d545 (change p 138 (some 116)) = d543 p := by
  change d544 (change p 138 (some 116)) = d543 p
  exact sub4479 p
theorem sub4481 (p : Pattern) : d547 (change p 138 (some 116)) = d543 p := by
  change d543 (change p 138 (some 116)) = d543 p
  exact sub4478 p
theorem sub4482 (p : Pattern) : d548 (change p 138 (some 116)) = d543 p := by
  change d547 (change p 138 (some 116)) = d543 p
  exact sub4481 p
theorem sub4483 (p : Pattern) : d549 (change p 138 (some 116)) = d543 p := by
  change (if p 115 then d548 (change p 138 (some 116)) else d545 (change p 138 (some 116))) = d543 p
  rw [sub4482, sub4480]
  simp only [ite_self]
theorem sub4484 (p : Pattern) : d551 (change p 138 (some 116)) = d543 p := by
  change d543 (change p 138 (some 116)) = d543 p
  exact sub4478 p
theorem sub4485 (p : Pattern) : d552 (change p 138 (some 116)) = d543 p := by
  change d551 (change p 138 (some 116)) = d543 p
  exact sub4484 p
theorem sub4486 (p : Pattern) : d554 (change p 138 (some 116)) = d543 p := by
  change d547 (change p 138 (some 116)) = d543 p
  exact sub4481 p
theorem sub4487 (p : Pattern) : d555 (change p 138 (some 116)) = d543 p := by
  change (if p 115 then d554 (change p 138 (some 116)) else d552 (change p 138 (some 116))) = d543 p
  rw [sub4486, sub4485]
  simp only [ite_self]
theorem sub4488 (p : Pattern) : d556 (change p 138 (some 116)) = d543 p := by
  change (if p 71 then d555 (change p 138 (some 116)) else d549 (change p 138 (some 116))) = d543 p
  rw [sub4487, sub4483]
  simp only [ite_self]
theorem sub4489 (p : Pattern) : d1 (change p 138 (some 116)) = d1 p := by
  rfl
theorem sub4490 (p : Pattern) : d102 (change p 138 (some 116)) = d102 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d1 (change p 138 (some 116))) = d102 p
  rw [sub4403, sub4489]
  rfl
theorem sub4491 (p : Pattern) : d103 (change p 138 (some 116)) = d103 p := by
  change (if p 246 then d102 (change p 138 (some 116)) else d1 (change p 138 (some 116))) = d103 p
  rw [sub4490, sub4489]
  rfl
theorem sub4492 (p : Pattern) : d104 (change p 138 (some 116)) = d104 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d103 (change p 138 (some 116))) = d104 p
  rw [sub4403, sub4491]
  rfl
theorem sub4493 (p : Pattern) : d105 (change p 138 (some 116)) = d105 p := by
  change (if p 182 then d104 (change p 138 (some 116)) else d103 (change p 138 (some 116))) = d105 p
  rw [sub4492, sub4491]
  rfl
theorem sub4494 (p : Pattern) : d5 (change p 138 (some 116)) = d5 p := by
  rfl
theorem sub4495 (p : Pattern) : d106 (change p 138 (some 116)) = d106 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d5 (change p 138 (some 116))) = d106 p
  rw [sub4403, sub4494]
  rfl
theorem sub4496 (p : Pattern) : d107 (change p 138 (some 116)) = d107 p := by
  change (if p 246 then d106 (change p 138 (some 116)) else d5 (change p 138 (some 116))) = d107 p
  rw [sub4495, sub4494]
  rfl
theorem sub4497 (p : Pattern) : d108 (change p 138 (some 116)) = d108 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d107 (change p 138 (some 116))) = d108 p
  rw [sub4403, sub4496]
  rfl
theorem sub4498 (p : Pattern) : d109 (change p 138 (some 116)) = d109 p := by
  change (if p 182 then d108 (change p 138 (some 116)) else d107 (change p 138 (some 116))) = d109 p
  rw [sub4497, sub4496]
  rfl
theorem sub4499 (p : Pattern) : d110 (change p 138 (some 116)) = d110 p := by
  change (if p 163 then d109 (change p 138 (some 116)) else d105 (change p 138 (some 116))) = d110 p
  rw [sub4498, sub4493]
  rfl
theorem sub4500 (p : Pattern) : d111 (change p 138 (some 116)) = d111 p := by
  change (if p 162 then d110 (change p 138 (some 116)) else d105 (change p 138 (some 116))) = d111 p
  rw [sub4499, sub4493]
  rfl
theorem sub4501 (p : Pattern) : d112 (change p 138 (some 116)) = d112 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d60 (change p 138 (some 116))) = d112 p
  rw [sub4403, sub4456]
  rfl
theorem sub4502 (p : Pattern) : d113 (change p 138 (some 116)) = d113 p := by
  change (if p 162 then d112 (change p 138 (some 116)) else d110 (change p 138 (some 116))) = d113 p
  rw [sub4501, sub4499]
  rfl
theorem sub4503 (p : Pattern) : d114 (change p 138 (some 116)) = d114 p := by
  change (if p 161 then d113 (change p 138 (some 116)) else d111 (change p 138 (some 116))) = d114 p
  rw [sub4502, sub4500]
  rfl
theorem sub4504 (p : Pattern) : d558 (change p 138 (some 116)) = d558 p := by
  change (if p 204 then d107 (change p 138 (some 116)) else d103 (change p 138 (some 116))) = d558 p
  rw [sub4496, sub4491]
  rfl
theorem sub4505 (p : Pattern) : d7 (change p 138 (some 116)) = d7 p := by
  rfl
theorem sub4506 (p : Pattern) : d119 (change p 138 (some 116)) = d119 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d7 (change p 138 (some 116))) = d119 p
  rw [sub4403, sub4505]
  rfl
theorem sub4507 (p : Pattern) : d120 (change p 138 (some 116)) = d120 p := by
  change (if p 246 then d119 (change p 138 (some 116)) else d7 (change p 138 (some 116))) = d120 p
  rw [sub4506, sub4505]
  rfl
theorem sub4508 (p : Pattern) : d121 (change p 138 (some 116)) = d121 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d120 (change p 138 (some 116))) = d121 p
  rw [sub4403, sub4507]
  rfl
theorem sub4509 (p : Pattern) : d559 (change p 138 (some 116)) = d559 p := by
  change (if p 182 then d121 (change p 138 (some 116)) else d558 (change p 138 (some 116))) = d559 p
  rw [sub4508, sub4504]
  rfl
theorem sub4510 (p : Pattern) : d560 (change p 138 (some 116)) = d560 p := by
  change (if p 182 then d41 (change p 138 (some 116)) else d558 (change p 138 (some 116))) = d560 p
  rw [sub4461, sub4504]
  rfl
theorem sub4511 (p : Pattern) : d561 (change p 138 (some 116)) = d561 p := by
  change (if p 163 then d560 (change p 138 (some 116)) else d559 (change p 138 (some 116))) = d561 p
  rw [sub4510, sub4509]
  rfl
theorem sub4512 (p : Pattern) : d562 (change p 138 (some 116)) = d562 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d558 (change p 138 (some 116))) = d562 p
  rw [sub4403, sub4504]
  rfl
theorem sub4513 (p : Pattern) : d563 (change p 138 (some 116)) = d563 p := by
  change (if p 204 then d24 (change p 138 (some 116)) else d107 (change p 138 (some 116))) = d563 p
  rw [sub4417, sub4496]
  rfl
theorem sub4514 (p : Pattern) : d564 (change p 138 (some 116)) = d564 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d563 (change p 138 (some 116))) = d564 p
  rw [sub4403, sub4513]
  rfl
theorem sub4515 (p : Pattern) : d565 (change p 138 (some 116)) = d565 p := by
  change (if p 163 then d564 (change p 138 (some 116)) else d562 (change p 138 (some 116))) = d565 p
  rw [sub4514, sub4512]
  rfl
theorem sub4516 (p : Pattern) : d566 (change p 138 (some 116)) = d566 p := by
  change (if p 162 then d565 (change p 138 (some 116)) else d561 (change p 138 (some 116))) = d566 p
  rw [sub4515, sub4511]
  rfl
theorem sub4517 (p : Pattern) : d278 (change p 138 (some 116)) = d278 p := by
  change (if p 163 then d12 (change p 138 (some 116)) else d277 (change p 138 (some 116))) = d278 p
  rw [sub4403, sub4471]
  rfl
theorem sub4518 (p : Pattern) : d567 (change p 138 (some 116)) = d567 p := by
  change (if p 162 then d278 (change p 138 (some 116)) else d565 (change p 138 (some 116))) = d567 p
  rw [sub4517, sub4515]
  rfl
theorem sub4519 (p : Pattern) : d568 (change p 138 (some 116)) = d568 p := by
  change (if p 161 then d567 (change p 138 (some 116)) else d566 (change p 138 (some 116))) = d568 p
  rw [sub4518, sub4516]
  rfl
theorem sub4520 (p : Pattern) : d569 (change p 138 (some 116)) = d569 p := by
  change (if p 160 then d568 (change p 138 (some 116)) else d114 (change p 138 (some 116))) = d569 p
  rw [sub4519, sub4503]
  rfl
theorem sub4521 (p : Pattern) : d3 (change p 138 (some 116)) = d3 p := by
  rfl
theorem sub4522 (p : Pattern) : d115 (change p 138 (some 116)) = d115 p := by
  change (if p 247 then d12 (change p 138 (some 116)) else d3 (change p 138 (some 116))) = d115 p
  rw [sub4403, sub4521]
  rfl
theorem sub4523 (p : Pattern) : d116 (change p 138 (some 116)) = d116 p := by
  change (if p 246 then d115 (change p 138 (some 116)) else d3 (change p 138 (some 116))) = d116 p
  rw [sub4522, sub4521]
  rfl
theorem sub4524 (p : Pattern) : d117 (change p 138 (some 116)) = d117 p := by
  change (if p 204 then d12 (change p 138 (some 116)) else d116 (change p 138 (some 116))) = d117 p
  rw [sub4403, sub4523]
  rfl
theorem sub4525 (p : Pattern) : d132 (change p 138 (some 116)) = d132 p := by
  change (if p 182 then d117 (change p 138 (some 116)) else d116 (change p 138 (some 116))) = d132 p
  rw [sub4524, sub4523]
  rfl
theorem sub4526 (p : Pattern) : d133 (change p 138 (some 116)) = d133 p := by
  change (if p 163 then d132 (change p 138 (some 116)) else d105 (change p 138 (some 116))) = d133 p
  rw [sub4525, sub4493]
  rfl
theorem sub4527 (p : Pattern) : d134 (change p 138 (some 116)) = d134 p := by
  change (if p 163 then d60 (change p 138 (some 116)) else d109 (change p 138 (some 116))) = d134 p
  rw [sub4456, sub4498]
  rfl
theorem sub4528 (p : Pattern) : d135 (change p 138 (some 116)) = d135 p := by
  change (if p 162 then d134 (change p 138 (some 116)) else d133 (change p 138 (some 116))) = d135 p
  rw [sub4527, sub4526]
  rfl
theorem sub4529 (p : Pattern) : d136 (change p 138 (some 116)) = d136 p := by
  change (if p 163 then d62 (change p 138 (some 116)) else d109 (change p 138 (some 116))) = d136 p
  rw [sub4462, sub4498]
  rfl
theorem sub4530 (p : Pattern) : d137 (change p 138 (some 116)) = d137 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d136 (change p 138 (some 116))) = d137 p
  rw [sub4403, sub4529]
  rfl
theorem sub4531 (p : Pattern) : d138 (change p 138 (some 116)) = d138 p := by
  change (if p 161 then d137 (change p 138 (some 116)) else d135 (change p 138 (some 116))) = d138 p
  rw [sub4530, sub4528]
  rfl
theorem sub4532 (p : Pattern) : d570 (change p 138 (some 116)) = d570 p := by
  change (if p 204 then d120 (change p 138 (some 116)) else d116 (change p 138 (some 116))) = d570 p
  rw [sub4507, sub4523]
  rfl
theorem sub4533 (p : Pattern) : d571 (change p 138 (some 116)) = d571 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d570 (change p 138 (some 116))) = d571 p
  rw [sub4403, sub4532]
  rfl
theorem sub4534 (p : Pattern) : d572 (change p 138 (some 116)) = d572 p := by
  change (if p 163 then d571 (change p 138 (some 116)) else d560 (change p 138 (some 116))) = d572 p
  rw [sub4533, sub4510]
  rfl
theorem sub4535 (p : Pattern) : d573 (change p 138 (some 116)) = d573 p := by
  change (if p 163 then d277 (change p 138 (some 116)) else d564 (change p 138 (some 116))) = d573 p
  rw [sub4471, sub4514]
  rfl
theorem sub4536 (p : Pattern) : d574 (change p 138 (some 116)) = d574 p := by
  change (if p 162 then d573 (change p 138 (some 116)) else d572 (change p 138 (some 116))) = d574 p
  rw [sub4535, sub4534]
  rfl
theorem sub4537 (p : Pattern) : d575 (change p 138 (some 116)) = d575 p := by
  change (if p 163 then d538 (change p 138 (some 116)) else d564 (change p 138 (some 116))) = d575 p
  rw [sub4473, sub4514]
  rfl
theorem sub4538 (p : Pattern) : d576 (change p 138 (some 116)) = d576 p := by
  change (if p 162 then d12 (change p 138 (some 116)) else d575 (change p 138 (some 116))) = d576 p
  rw [sub4403, sub4537]
  rfl
theorem sub4539 (p : Pattern) : d577 (change p 138 (some 116)) = d577 p := by
  change (if p 161 then d576 (change p 138 (some 116)) else d574 (change p 138 (some 116))) = d577 p
  rw [sub4538, sub4536]
  rfl
theorem sub4540 (p : Pattern) : d578 (change p 138 (some 116)) = d578 p := by
  change (if p 160 then d577 (change p 138 (some 116)) else d138 (change p 138 (some 116))) = d578 p
  rw [sub4539, sub4531]
  rfl
theorem sub4541 (p : Pattern) : d579 (change p 138 (some 116)) = d579 p := by
  change (if p 141 then d578 (change p 138 (some 116)) else d569 (change p 138 (some 116))) = d579 p
  rw [sub4540, sub4520]
  rfl
theorem sub4542 (p : Pattern) : d580 (change p 138 (some 116)) = d579 p := by
  change d579 (change p 138 (some 116)) = d579 p
  exact sub4541 p
theorem sub4543 (p : Pattern) : d581 (change p 138 (some 116)) = d579 p := by
  change d580 (change p 138 (some 116)) = d579 p
  exact sub4542 p
theorem sub4544 (p : Pattern) : d583 (change p 138 (some 116)) = d579 p := by
  change d579 (change p 138 (some 116)) = d579 p
  exact sub4541 p
theorem sub4545 (p : Pattern) : d584 (change p 138 (some 116)) = d579 p := by
  change d583 (change p 138 (some 116)) = d579 p
  exact sub4544 p
theorem sub4546 (p : Pattern) : d585 (change p 138 (some 116)) = d579 p := by
  change (if p 115 then d584 (change p 138 (some 116)) else d581 (change p 138 (some 116))) = d579 p
  rw [sub4545, sub4543]
  simp only [ite_self]
theorem sub4547 (p : Pattern) : d586 (change p 138 (some 116)) = d4463 p := by
  change (if p 71 then d585 (change p 138 (some 116)) else d549 (change p 138 (some 116))) = d4463 p
  rw [sub4546, sub4483]
  rfl
theorem sub4548 (p : Pattern) : d587 (change p 138 (some 116)) = d4464 p := by
  change (if p 49 then d586 (change p 138 (some 116)) else d556 (change p 138 (some 116))) = d4464 p
  rw [sub4547, sub4488]
  rfl
theorem sub4549 (p : Pattern) : d78 (change p 138 (some 116)) = d78 p := by
  change (if p 182 then d36 (change p 138 (some 116)) else d35 (change p 138 (some 116))) = d78 p
  rw [sub4427, sub4426]
  rfl
theorem sub4550 (p : Pattern) : d79 (change p 138 (some 116)) = d79 p := by
  change (if p 163 then d78 (change p 138 (some 116)) else d53 (change p 138 (some 116))) = d79 p
  rw [sub4549, sub4452]
  rfl
theorem sub4551 (p : Pattern) : d188 (change p 138 (some 116)) = d188 p := by
  change (if p 162 then d79 (change p 138 (some 116)) else d16 (change p 138 (some 116))) = d188 p
  rw [sub4550, sub4407]
  rfl
theorem sub4552 (p : Pattern) : d80 (change p 138 (some 116)) = d80 p := by
  change (if p 162 then d63 (change p 138 (some 116)) else d79 (change p 138 (some 116))) = d80 p
  rw [sub4463, sub4550]
  rfl
theorem sub4553 (p : Pattern) : d189 (change p 138 (some 116)) = d189 p := by
  change (if p 161 then d80 (change p 138 (some 116)) else d188 (change p 138 (some 116))) = d189 p
  rw [sub4552, sub4551]
  rfl
theorem sub4554 (p : Pattern) : d588 (change p 138 (some 116)) = d588 p := by
  change (if p 204 then d18 (change p 138 (some 116)) else d31 (change p 138 (some 116))) = d588 p
  rw [sub4410, sub4450]
  rfl
theorem sub4555 (p : Pattern) : d589 (change p 138 (some 116)) = d589 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d588 (change p 138 (some 116))) = d589 p
  rw [sub4403, sub4554]
  rfl
theorem sub4556 (p : Pattern) : d590 (change p 138 (some 116)) = d590 p := by
  change (if p 204 then d191 (change p 138 (some 116)) else d35 (change p 138 (some 116))) = d590 p
  rw [sub4438, sub4426]
  rfl
theorem sub4557 (p : Pattern) : d591 (change p 138 (some 116)) = d591 p := by
  change (if p 182 then d12 (change p 138 (some 116)) else d590 (change p 138 (some 116))) = d591 p
  rw [sub4403, sub4556]
  rfl
theorem sub4558 (p : Pattern) : d592 (change p 138 (some 116)) = d592 p := by
  change (if p 163 then d591 (change p 138 (some 116)) else d589 (change p 138 (some 116))) = d592 p
  rw [sub4557, sub4555]
  rfl
theorem sub4559 (p : Pattern) : d593 (change p 138 (some 116)) = d593 p := by
  change (if p 162 then d592 (change p 138 (some 116)) else d521 (change p 138 (some 116))) = d593 p
  rw [sub4558, sub4434]
  rfl
end NetHack.Sokoban22Refined85
