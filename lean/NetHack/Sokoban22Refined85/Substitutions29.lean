/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3480 (p : Pattern) : d295 (change p 116 none) = d295 p := by
  change (if p 162 then d278 (change p 116 none) else d293 (change p 116 none)) = d295 p
  rw [sub3463, sub3478]
  rfl
theorem sub3481 (p : Pattern) : d296 (change p 116 none) = d296 p := by
  change (if p 161 then d295 (change p 116 none) else d294 (change p 116 none)) = d296 p
  rw [sub3480, sub3479]
  rfl
theorem sub3482 (p : Pattern) : d297 (change p 116 none) = d297 p := by
  change (if p 160 then d151 (change p 116 none) else d296 (change p 116 none)) = d297 p
  rw [sub3426, sub3481]
  rfl
theorem sub3483 (p : Pattern) : d298 (change p 116 none) = d298 p := by
  change (if p 182 then d108 (change p 116 none) else d282 (change p 116 none)) = d298 p
  rw [sub3381, sub3467]
  rfl
theorem sub3484 (p : Pattern) : d299 (change p 116 none) = d299 p := by
  change (if p 163 then d298 (change p 116 none) else d269 (change p 116 none)) = d299 p
  rw [sub3483, sub3454]
  rfl
theorem sub3485 (p : Pattern) : d300 (change p 116 none) = d300 p := by
  change (if p 163 then d12 (change p 116 none) else d292 (change p 116 none)) = d300 p
  rw [sub3283, sub3477]
  rfl
theorem sub3486 (p : Pattern) : d301 (change p 116 none) = d301 p := by
  change (if p 162 then d300 (change p 116 none) else d299 (change p 116 none)) = d301 p
  rw [sub3485, sub3484]
  rfl
theorem sub3487 (p : Pattern) : d302 (change p 116 none) = d302 p := by
  change (if p 162 then d12 (change p 116 none) else d300 (change p 116 none)) = d302 p
  rw [sub3283, sub3485]
  rfl
theorem sub3488 (p : Pattern) : d303 (change p 116 none) = d303 p := by
  change (if p 161 then d302 (change p 116 none) else d301 (change p 116 none)) = d303 p
  rw [sub3487, sub3486]
  rfl
theorem sub3489 (p : Pattern) : d304 (change p 116 none) = d304 p := by
  change (if p 160 then d155 (change p 116 none) else d303 (change p 116 none)) = d304 p
  rw [sub3430, sub3488]
  rfl
theorem sub3490 (p : Pattern) : d305 (change p 116 none) = d305 p := by
  change (if p 141 then d304 (change p 116 none) else d297 (change p 116 none)) = d305 p
  rw [sub3489, sub3482]
  rfl
theorem sub3491 (p : Pattern) : d306 (change p 116 none) = d306 p := by
  change (if p 138 then d305 (change p 116 none) else d290 (change p 116 none)) = d306 p
  rw [sub3490, sub3475]
  rfl
theorem sub3492 (p : Pattern) : d512 (change p 116 none) = d306 p := by
  change d306 (change p 116 none) = d306 p
  exact sub3491 p
theorem sub3493 (p : Pattern) : d513 (change p 116 none) = d4199 p := by
  change (if p 115 then d512 (change p 116 none) else d511 (change p 116 none)) = d4199 p
  rw [sub3492, sub3452]
  rfl
theorem sub3494 (p : Pattern) : d514 (change p 116 none) = d4200 p := by
  change (if p 71 then d513 (change p 116 none) else d501 (change p 116 none)) = d4200 p
  rw [sub3493, sub3368]
  rfl
theorem sub3495 (p : Pattern) : d515 (change p 116 none) = d4201 p := by
  change (if p 49 then d514 (change p 116 none) else d505 (change p 116 none)) = d4201 p
  rw [sub3494, sub3372]
  rfl
theorem sub3496 (p : Pattern) : d516 (change p 116 none) = d4202 p := by
  change (if p 48 then d515 (change p 116 none) else d510 (change p 116 none)) = d4202 p
  rw [sub3495, sub3438]
  rfl
theorem sub3497 (p : Pattern) : d0 (change p 160 (some 182)) = d0 p := by
  rfl
theorem sub3498 (p : Pattern) : d12 (change p 160 (some 182)) = d12 p := by
  rfl
theorem sub3499 (p : Pattern) : d13 (change p 160 (some 182)) = d13 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d0 (change p 160 (some 182))) = d13 p
  rw [sub3498, sub3497]
  rfl
theorem sub3500 (p : Pattern) : d14 (change p 160 (some 182)) = d14 p := by
  change (if p 246 then d13 (change p 160 (some 182)) else d0 (change p 160 (some 182))) = d14 p
  rw [sub3499, sub3497]
  rfl
theorem sub3501 (p : Pattern) : d15 (change p 160 (some 182)) = d15 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d14 (change p 160 (some 182))) = d15 p
  rw [sub3498, sub3500]
  rfl
theorem sub3502 (p : Pattern) : d16 (change p 160 (some 182)) = d15 p := by
  change d15 (change p 160 (some 182)) = d15 p
  exact sub3501 p
theorem sub3503 (p : Pattern) : d4 (change p 160 (some 182)) = d4 p := by
  rfl
theorem sub3504 (p : Pattern) : d17 (change p 160 (some 182)) = d17 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d4 (change p 160 (some 182))) = d17 p
  rw [sub3498, sub3503]
  rfl
theorem sub3505 (p : Pattern) : d18 (change p 160 (some 182)) = d18 p := by
  change (if p 246 then d17 (change p 160 (some 182)) else d4 (change p 160 (some 182))) = d18 p
  rw [sub3504, sub3503]
  rfl
theorem sub3506 (p : Pattern) : d19 (change p 160 (some 182)) = d19 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d18 (change p 160 (some 182))) = d19 p
  rw [sub3498, sub3505]
  rfl
theorem sub3507 (p : Pattern) : d20 (change p 160 (some 182)) = d19 p := by
  change d19 (change p 160 (some 182)) = d19 p
  exact sub3506 p
theorem sub3508 (p : Pattern) : d21 (change p 160 (some 182)) = d4209 p := by
  change (if p 163 then d20 (change p 160 (some 182)) else d16 (change p 160 (some 182))) = d4209 p
  rw [sub3507, sub3502]
  rfl
theorem sub3509 (p : Pattern) : d22 (change p 160 (some 182)) = d4210 p := by
  change (if p 162 then d21 (change p 160 (some 182)) else d16 (change p 160 (some 182))) = d4210 p
  rw [sub3508, sub3502]
  rfl
theorem sub3510 (p : Pattern) : d9 (change p 160 (some 182)) = d9 p := by
  rfl
theorem sub3511 (p : Pattern) : d23 (change p 160 (some 182)) = d23 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d9 (change p 160 (some 182))) = d23 p
  rw [sub3498, sub3510]
  rfl
theorem sub3512 (p : Pattern) : d24 (change p 160 (some 182)) = d24 p := by
  change (if p 246 then d23 (change p 160 (some 182)) else d9 (change p 160 (some 182))) = d24 p
  rw [sub3511, sub3510]
  rfl
theorem sub3513 (p : Pattern) : d25 (change p 160 (some 182)) = d25 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d24 (change p 160 (some 182))) = d25 p
  rw [sub3498, sub3512]
  rfl
theorem sub3514 (p : Pattern) : d26 (change p 160 (some 182)) = d25 p := by
  change d25 (change p 160 (some 182)) = d25 p
  exact sub3513 p
theorem sub3515 (p : Pattern) : d27 (change p 160 (some 182)) = d4211 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d26 (change p 160 (some 182))) = d4211 p
  rw [sub3498, sub3514]
  rfl
theorem sub3516 (p : Pattern) : d28 (change p 160 (some 182)) = d4212 p := by
  change (if p 162 then d27 (change p 160 (some 182)) else d21 (change p 160 (some 182))) = d4212 p
  rw [sub3515, sub3508]
  rfl
theorem sub3517 (p : Pattern) : d29 (change p 160 (some 182)) = d4213 p := by
  change (if p 161 then d28 (change p 160 (some 182)) else d22 (change p 160 (some 182))) = d4213 p
  rw [sub3516, sub3509]
  rfl
theorem sub3518 (p : Pattern) : d710 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3519 (p : Pattern) : d2 (change p 160 (some 182)) = d2 p := by
  rfl
theorem sub3520 (p : Pattern) : d30 (change p 160 (some 182)) = d30 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d2 (change p 160 (some 182))) = d30 p
  rw [sub3498, sub3519]
  rfl
theorem sub3521 (p : Pattern) : d31 (change p 160 (some 182)) = d31 p := by
  change (if p 246 then d30 (change p 160 (some 182)) else d2 (change p 160 (some 182))) = d31 p
  rw [sub3520, sub3519]
  rfl
theorem sub3522 (p : Pattern) : d32 (change p 160 (some 182)) = d32 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d31 (change p 160 (some 182))) = d32 p
  rw [sub3498, sub3521]
  rfl
theorem sub3523 (p : Pattern) : d53 (change p 160 (some 182)) = d32 p := by
  change d32 (change p 160 (some 182)) = d32 p
  exact sub3522 p
theorem sub3524 (p : Pattern) : d54 (change p 160 (some 182)) = d4214 p := by
  change (if p 163 then d53 (change p 160 (some 182)) else d16 (change p 160 (some 182))) = d4214 p
  rw [sub3523, sub3502]
  rfl
theorem sub3525 (p : Pattern) : d55 (change p 160 (some 182)) = d4215 p := by
  change (if p 163 then d26 (change p 160 (some 182)) else d20 (change p 160 (some 182))) = d4215 p
  rw [sub3514, sub3507]
  rfl
theorem sub3526 (p : Pattern) : d56 (change p 160 (some 182)) = d4216 p := by
  change (if p 162 then d55 (change p 160 (some 182)) else d54 (change p 160 (some 182))) = d4216 p
  rw [sub3525, sub3524]
  rfl
theorem sub3527 (p : Pattern) : d10 (change p 160 (some 182)) = d10 p := by
  rfl
theorem sub3528 (p : Pattern) : d57 (change p 160 (some 182)) = d57 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d10 (change p 160 (some 182))) = d57 p
  rw [sub3498, sub3527]
  rfl
theorem sub3529 (p : Pattern) : d58 (change p 160 (some 182)) = d58 p := by
  change (if p 246 then d57 (change p 160 (some 182)) else d10 (change p 160 (some 182))) = d58 p
  rw [sub3528, sub3527]
  rfl
theorem sub3530 (p : Pattern) : d59 (change p 160 (some 182)) = d59 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d58 (change p 160 (some 182))) = d59 p
  rw [sub3498, sub3529]
  rfl
theorem sub3531 (p : Pattern) : d60 (change p 160 (some 182)) = d59 p := by
  change d59 (change p 160 (some 182)) = d59 p
  exact sub3530 p
theorem sub3532 (p : Pattern) : d61 (change p 160 (some 182)) = d4217 p := by
  change (if p 163 then d60 (change p 160 (some 182)) else d20 (change p 160 (some 182))) = d4217 p
  rw [sub3531, sub3507]
  rfl
theorem sub3533 (p : Pattern) : d11 (change p 160 (some 182)) = d11 p := by
  rfl
theorem sub3534 (p : Pattern) : d39 (change p 160 (some 182)) = d39 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d11 (change p 160 (some 182))) = d39 p
  rw [sub3498, sub3533]
  rfl
theorem sub3535 (p : Pattern) : d40 (change p 160 (some 182)) = d40 p := by
  change (if p 246 then d39 (change p 160 (some 182)) else d11 (change p 160 (some 182))) = d40 p
  rw [sub3534, sub3533]
  rfl
theorem sub3536 (p : Pattern) : d41 (change p 160 (some 182)) = d41 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d40 (change p 160 (some 182))) = d41 p
  rw [sub3498, sub3535]
  rfl
theorem sub3537 (p : Pattern) : d62 (change p 160 (some 182)) = d41 p := by
  change d41 (change p 160 (some 182)) = d41 p
  exact sub3536 p
theorem sub3538 (p : Pattern) : d63 (change p 160 (some 182)) = d4218 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d62 (change p 160 (some 182))) = d4218 p
  rw [sub3498, sub3537]
  rfl
theorem sub3539 (p : Pattern) : d64 (change p 160 (some 182)) = d4219 p := by
  change (if p 162 then d63 (change p 160 (some 182)) else d61 (change p 160 (some 182))) = d4219 p
  rw [sub3538, sub3532]
  rfl
theorem sub3540 (p : Pattern) : d65 (change p 160 (some 182)) = d4220 p := by
  change (if p 161 then d64 (change p 160 (some 182)) else d56 (change p 160 (some 182))) = d4220 p
  rw [sub3539, sub3526]
  rfl
theorem sub3541 (p : Pattern) : d711 (change p 160 (some 182)) = d4220 p := by
  change d65 (change p 160 (some 182)) = d4220 p
  exact sub3540 p
theorem sub3542 (p : Pattern) : d712 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d711 (change p 160 (some 182)) else d710 (change p 160 (some 182))) = d4221 p
  rw [sub3541, sub3518]
  rfl
theorem sub3543 (p : Pattern) : d713 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3544 (p : Pattern) : d714 (change p 160 (some 182)) = d4220 p := by
  change d65 (change p 160 (some 182)) = d4220 p
  exact sub3540 p
theorem sub3545 (p : Pattern) : d715 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d714 (change p 160 (some 182)) else d713 (change p 160 (some 182))) = d4221 p
  rw [sub3544, sub3543]
  rfl
theorem sub3546 (p : Pattern) : d716 (change p 160 (some 182)) = d4221 p := by
  change (if p 138 then d715 (change p 160 (some 182)) else d712 (change p 160 (some 182))) = d4221 p
  rw [sub3545, sub3542]
  simp only [ite_self]
theorem sub3547 (p : Pattern) : d717 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3548 (p : Pattern) : d718 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d714 (change p 160 (some 182)) else d717 (change p 160 (some 182))) = d4221 p
  rw [sub3544, sub3547]
  rfl
theorem sub3549 (p : Pattern) : d89 (change p 160 (some 182)) = d4222 p := by
  change (if p 163 then d62 (change p 160 (some 182)) else d26 (change p 160 (some 182))) = d4222 p
  rw [sub3537, sub3514]
  rfl
theorem sub3550 (p : Pattern) : d90 (change p 160 (some 182)) = d4223 p := by
  change (if p 162 then d63 (change p 160 (some 182)) else d89 (change p 160 (some 182))) = d4223 p
  rw [sub3538, sub3549]
  rfl
theorem sub3551 (p : Pattern) : d91 (change p 160 (some 182)) = d4224 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d63 (change p 160 (some 182))) = d4224 p
  rw [sub3498, sub3538]
  rfl
theorem sub3552 (p : Pattern) : d92 (change p 160 (some 182)) = d4225 p := by
  change (if p 161 then d91 (change p 160 (some 182)) else d90 (change p 160 (some 182))) = d4225 p
  rw [sub3551, sub3550]
  rfl
theorem sub3553 (p : Pattern) : d719 (change p 160 (some 182)) = d4225 p := by
  change d92 (change p 160 (some 182)) = d4225 p
  exact sub3552 p
theorem sub3554 (p : Pattern) : d93 (change p 160 (some 182)) = d4226 p := by
  change (if p 161 then d12 (change p 160 (some 182)) else d91 (change p 160 (some 182))) = d4226 p
  rw [sub3498, sub3551]
  rfl
theorem sub3555 (p : Pattern) : d95 (change p 160 (some 182)) = d4226 p := by
  change d93 (change p 160 (some 182)) = d4226 p
  exact sub3554 p
theorem sub3556 (p : Pattern) : d720 (change p 160 (some 182)) = d4227 p := by
  change (if p 141 then d95 (change p 160 (some 182)) else d719 (change p 160 (some 182))) = d4227 p
  rw [sub3555, sub3553]
  rfl
theorem sub3557 (p : Pattern) : d721 (change p 160 (some 182)) = d4228 p := by
  change (if p 138 then d720 (change p 160 (some 182)) else d718 (change p 160 (some 182))) = d4228 p
  rw [sub3556, sub3548]
  rfl
theorem sub3558 (p : Pattern) : d722 (change p 160 (some 182)) = d4229 p := by
  change (if p 116 then d721 (change p 160 (some 182)) else d716 (change p 160 (some 182))) = d4229 p
  rw [sub3557, sub3546]
  rfl
theorem sub3559 (p : Pattern) : d723 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3560 (p : Pattern) : d724 (change p 160 (some 182)) = d4220 p := by
  change d65 (change p 160 (some 182)) = d4220 p
  exact sub3540 p
theorem sub3561 (p : Pattern) : d725 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d724 (change p 160 (some 182)) else d723 (change p 160 (some 182))) = d4221 p
  rw [sub3560, sub3559]
  rfl
theorem sub3562 (p : Pattern) : d726 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3563 (p : Pattern) : d727 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d714 (change p 160 (some 182)) else d726 (change p 160 (some 182))) = d4221 p
  rw [sub3544, sub3562]
  rfl
theorem sub3564 (p : Pattern) : d728 (change p 160 (some 182)) = d4221 p := by
  change (if p 138 then d727 (change p 160 (some 182)) else d725 (change p 160 (some 182))) = d4221 p
  rw [sub3563, sub3561]
  simp only [ite_self]
theorem sub3565 (p : Pattern) : d729 (change p 160 (some 182)) = d4230 p := by
  change (if p 138 then d12 (change p 160 (some 182)) else d727 (change p 160 (some 182))) = d4230 p
  rw [sub3498, sub3563]
  rfl
theorem sub3566 (p : Pattern) : d730 (change p 160 (some 182)) = d4231 p := by
  change (if p 116 then d729 (change p 160 (some 182)) else d728 (change p 160 (some 182))) = d4231 p
  rw [sub3565, sub3564]
  rfl
theorem sub3567 (p : Pattern) : d731 (change p 160 (some 182)) = d4232 p := by
  change (if p 115 then d730 (change p 160 (some 182)) else d722 (change p 160 (some 182))) = d4232 p
  rw [sub3566, sub3558]
  rfl
theorem sub3568 (p : Pattern) : d732 (change p 160 (some 182)) = d4213 p := by
  change d29 (change p 160 (some 182)) = d4213 p
  exact sub3517 p
theorem sub3569 (p : Pattern) : d733 (change p 160 (some 182)) = d4220 p := by
  change d65 (change p 160 (some 182)) = d4220 p
  exact sub3540 p
theorem sub3570 (p : Pattern) : d734 (change p 160 (some 182)) = d4221 p := by
  change (if p 141 then d733 (change p 160 (some 182)) else d732 (change p 160 (some 182))) = d4221 p
  rw [sub3569, sub3568]
  rfl
theorem sub3571 (p : Pattern) : d735 (change p 160 (some 182)) = d4221 p := by
  change (if p 138 then d727 (change p 160 (some 182)) else d734 (change p 160 (some 182))) = d4221 p
  rw [sub3563, sub3570]
  simp only [ite_self]
theorem sub3572 (p : Pattern) : d736 (change p 160 (some 182)) = d4228 p := by
  change (if p 138 then d720 (change p 160 (some 182)) else d715 (change p 160 (some 182))) = d4228 p
  rw [sub3556, sub3545]
  rfl
theorem sub3573 (p : Pattern) : d737 (change p 160 (some 182)) = d4229 p := by
  change (if p 116 then d736 (change p 160 (some 182)) else d735 (change p 160 (some 182))) = d4229 p
  rw [sub3572, sub3571]
  rfl
theorem sub3574 (p : Pattern) : d738 (change p 160 (some 182)) = d4221 p := by
  change (if p 138 then d727 (change p 160 (some 182)) else d718 (change p 160 (some 182))) = d4221 p
  rw [sub3563, sub3548]
  simp only [ite_self]
theorem sub3575 (p : Pattern) : d739 (change p 160 (some 182)) = d4231 p := by
  change (if p 116 then d729 (change p 160 (some 182)) else d738 (change p 160 (some 182))) = d4231 p
  rw [sub3565, sub3574]
  rfl
theorem sub3576 (p : Pattern) : d740 (change p 160 (some 182)) = d4232 p := by
  change (if p 115 then d739 (change p 160 (some 182)) else d737 (change p 160 (some 182))) = d4232 p
  rw [sub3575, sub3573]
  rfl
theorem sub3577 (p : Pattern) : d741 (change p 160 (some 182)) = d4232 p := by
  change (if p 71 then d740 (change p 160 (some 182)) else d731 (change p 160 (some 182))) = d4232 p
  rw [sub3576, sub3567]
  simp only [ite_self]
theorem sub3578 (p : Pattern) : d1 (change p 160 (some 182)) = d1 p := by
  rfl
theorem sub3579 (p : Pattern) : d102 (change p 160 (some 182)) = d102 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d1 (change p 160 (some 182))) = d102 p
  rw [sub3498, sub3578]
  rfl
theorem sub3580 (p : Pattern) : d103 (change p 160 (some 182)) = d103 p := by
  change (if p 246 then d102 (change p 160 (some 182)) else d1 (change p 160 (some 182))) = d103 p
  rw [sub3579, sub3578]
  rfl
theorem sub3581 (p : Pattern) : d104 (change p 160 (some 182)) = d104 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d103 (change p 160 (some 182))) = d104 p
  rw [sub3498, sub3580]
  rfl
theorem sub3582 (p : Pattern) : d105 (change p 160 (some 182)) = d104 p := by
  change d104 (change p 160 (some 182)) = d104 p
  exact sub3581 p
theorem sub3583 (p : Pattern) : d5 (change p 160 (some 182)) = d5 p := by
  rfl
theorem sub3584 (p : Pattern) : d106 (change p 160 (some 182)) = d106 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d5 (change p 160 (some 182))) = d106 p
  rw [sub3498, sub3583]
  rfl
theorem sub3585 (p : Pattern) : d107 (change p 160 (some 182)) = d107 p := by
  change (if p 246 then d106 (change p 160 (some 182)) else d5 (change p 160 (some 182))) = d107 p
  rw [sub3584, sub3583]
  rfl
theorem sub3586 (p : Pattern) : d108 (change p 160 (some 182)) = d108 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d107 (change p 160 (some 182))) = d108 p
  rw [sub3498, sub3585]
  rfl
theorem sub3587 (p : Pattern) : d109 (change p 160 (some 182)) = d108 p := by
  change d108 (change p 160 (some 182)) = d108 p
  exact sub3586 p
theorem sub3588 (p : Pattern) : d110 (change p 160 (some 182)) = d4233 p := by
  change (if p 163 then d109 (change p 160 (some 182)) else d105 (change p 160 (some 182))) = d4233 p
  rw [sub3587, sub3582]
  rfl
theorem sub3589 (p : Pattern) : d111 (change p 160 (some 182)) = d4234 p := by
  change (if p 162 then d110 (change p 160 (some 182)) else d105 (change p 160 (some 182))) = d4234 p
  rw [sub3588, sub3582]
  rfl
theorem sub3590 (p : Pattern) : d112 (change p 160 (some 182)) = d4235 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d60 (change p 160 (some 182))) = d4235 p
  rw [sub3498, sub3531]
  rfl
theorem sub3591 (p : Pattern) : d113 (change p 160 (some 182)) = d4236 p := by
  change (if p 162 then d112 (change p 160 (some 182)) else d110 (change p 160 (some 182))) = d4236 p
  rw [sub3590, sub3588]
  rfl
theorem sub3592 (p : Pattern) : d114 (change p 160 (some 182)) = d4237 p := by
  change (if p 161 then d113 (change p 160 (some 182)) else d111 (change p 160 (some 182))) = d4237 p
  rw [sub3591, sub3589]
  rfl
theorem sub3593 (p : Pattern) : d742 (change p 160 (some 182)) = d4237 p := by
  change d114 (change p 160 (some 182)) = d4237 p
  exact sub3592 p
theorem sub3594 (p : Pattern) : d3 (change p 160 (some 182)) = d3 p := by
  rfl
theorem sub3595 (p : Pattern) : d115 (change p 160 (some 182)) = d115 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d3 (change p 160 (some 182))) = d115 p
  rw [sub3498, sub3594]
  rfl
theorem sub3596 (p : Pattern) : d116 (change p 160 (some 182)) = d116 p := by
  change (if p 246 then d115 (change p 160 (some 182)) else d3 (change p 160 (some 182))) = d116 p
  rw [sub3595, sub3594]
  rfl
theorem sub3597 (p : Pattern) : d117 (change p 160 (some 182)) = d117 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d116 (change p 160 (some 182))) = d117 p
  rw [sub3498, sub3596]
  rfl
theorem sub3598 (p : Pattern) : d132 (change p 160 (some 182)) = d117 p := by
  change d117 (change p 160 (some 182)) = d117 p
  exact sub3597 p
theorem sub3599 (p : Pattern) : d133 (change p 160 (some 182)) = d4238 p := by
  change (if p 163 then d132 (change p 160 (some 182)) else d105 (change p 160 (some 182))) = d4238 p
  rw [sub3598, sub3582]
  rfl
end NetHack.Sokoban22Refined85
