/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions29
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3600 (p : Pattern) : d134 (change p 160 (some 182)) = d4239 p := by
  change (if p 163 then d60 (change p 160 (some 182)) else d109 (change p 160 (some 182))) = d4239 p
  rw [sub3531, sub3587]
  rfl
theorem sub3601 (p : Pattern) : d135 (change p 160 (some 182)) = d4240 p := by
  change (if p 162 then d134 (change p 160 (some 182)) else d133 (change p 160 (some 182))) = d4240 p
  rw [sub3600, sub3599]
  rfl
theorem sub3602 (p : Pattern) : d136 (change p 160 (some 182)) = d4241 p := by
  change (if p 163 then d62 (change p 160 (some 182)) else d109 (change p 160 (some 182))) = d4241 p
  rw [sub3537, sub3587]
  rfl
theorem sub3603 (p : Pattern) : d137 (change p 160 (some 182)) = d4242 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d136 (change p 160 (some 182))) = d4242 p
  rw [sub3498, sub3602]
  rfl
theorem sub3604 (p : Pattern) : d138 (change p 160 (some 182)) = d4243 p := by
  change (if p 161 then d137 (change p 160 (some 182)) else d135 (change p 160 (some 182))) = d4243 p
  rw [sub3603, sub3601]
  rfl
theorem sub3605 (p : Pattern) : d743 (change p 160 (some 182)) = d4243 p := by
  change d138 (change p 160 (some 182)) = d4243 p
  exact sub3604 p
theorem sub3606 (p : Pattern) : d744 (change p 160 (some 182)) = d4244 p := by
  change (if p 141 then d743 (change p 160 (some 182)) else d742 (change p 160 (some 182))) = d4244 p
  rw [sub3605, sub3593]
  rfl
theorem sub3607 (p : Pattern) : d745 (change p 160 (some 182)) = d4237 p := by
  change d114 (change p 160 (some 182)) = d4237 p
  exact sub3592 p
theorem sub3608 (p : Pattern) : d746 (change p 160 (some 182)) = d4243 p := by
  change d138 (change p 160 (some 182)) = d4243 p
  exact sub3604 p
theorem sub3609 (p : Pattern) : d747 (change p 160 (some 182)) = d4244 p := by
  change (if p 141 then d746 (change p 160 (some 182)) else d745 (change p 160 (some 182))) = d4244 p
  rw [sub3608, sub3607]
  rfl
theorem sub3610 (p : Pattern) : d748 (change p 160 (some 182)) = d4244 p := by
  change (if p 138 then d747 (change p 160 (some 182)) else d744 (change p 160 (some 182))) = d4244 p
  rw [sub3609, sub3606]
  simp only [ite_self]
theorem sub3611 (p : Pattern) : d749 (change p 160 (some 182)) = d4237 p := by
  change d114 (change p 160 (some 182)) = d4237 p
  exact sub3592 p
theorem sub3612 (p : Pattern) : d750 (change p 160 (some 182)) = d4244 p := by
  change (if p 141 then d746 (change p 160 (some 182)) else d749 (change p 160 (some 182))) = d4244 p
  rw [sub3608, sub3611]
  rfl
theorem sub3613 (p : Pattern) : d159 (change p 160 (some 182)) = d4245 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d112 (change p 160 (some 182))) = d4245 p
  rw [sub3498, sub3590]
  rfl
theorem sub3614 (p : Pattern) : d160 (change p 160 (some 182)) = d4246 p := by
  change (if p 161 then d12 (change p 160 (some 182)) else d159 (change p 160 (some 182))) = d4246 p
  rw [sub3498, sub3613]
  rfl
theorem sub3615 (p : Pattern) : d161 (change p 160 (some 182)) = d4246 p := by
  change d160 (change p 160 (some 182)) = d4246 p
  exact sub3614 p
theorem sub3616 (p : Pattern) : d162 (change p 160 (some 182)) = d4247 p := by
  change (if p 141 then d12 (change p 160 (some 182)) else d161 (change p 160 (some 182))) = d4247 p
  rw [sub3498, sub3615]
  rfl
theorem sub3617 (p : Pattern) : d751 (change p 160 (some 182)) = d4248 p := by
  change (if p 138 then d162 (change p 160 (some 182)) else d750 (change p 160 (some 182))) = d4248 p
  rw [sub3616, sub3612]
  rfl
theorem sub3618 (p : Pattern) : d752 (change p 160 (some 182)) = d4249 p := by
  change (if p 116 then d751 (change p 160 (some 182)) else d748 (change p 160 (some 182))) = d4249 p
  rw [sub3617, sub3610]
  rfl
theorem sub3619 (p : Pattern) : d753 (change p 160 (some 182)) = d4237 p := by
  change d114 (change p 160 (some 182)) = d4237 p
  exact sub3592 p
theorem sub3620 (p : Pattern) : d754 (change p 160 (some 182)) = d4244 p := by
  change (if p 141 then d746 (change p 160 (some 182)) else d753 (change p 160 (some 182))) = d4244 p
  rw [sub3608, sub3619]
  rfl
theorem sub3621 (p : Pattern) : d755 (change p 160 (some 182)) = d4244 p := by
  change (if p 138 then d747 (change p 160 (some 182)) else d754 (change p 160 (some 182))) = d4244 p
  rw [sub3609, sub3620]
  simp only [ite_self]
theorem sub3622 (p : Pattern) : d756 (change p 160 (some 182)) = d4250 p := by
  change (if p 138 then d12 (change p 160 (some 182)) else d747 (change p 160 (some 182))) = d4250 p
  rw [sub3498, sub3609]
  rfl
theorem sub3623 (p : Pattern) : d757 (change p 160 (some 182)) = d4251 p := by
  change (if p 116 then d756 (change p 160 (some 182)) else d755 (change p 160 (some 182))) = d4251 p
  rw [sub3622, sub3621]
  rfl
theorem sub3624 (p : Pattern) : d758 (change p 160 (some 182)) = d4252 p := by
  change (if p 115 then d757 (change p 160 (some 182)) else d752 (change p 160 (some 182))) = d4252 p
  rw [sub3623, sub3618]
  rfl
theorem sub3625 (p : Pattern) : d759 (change p 160 (some 182)) = d4253 p := by
  change (if p 71 then d758 (change p 160 (some 182)) else d731 (change p 160 (some 182))) = d4253 p
  rw [sub3624, sub3567]
  rfl
theorem sub3626 (p : Pattern) : d760 (change p 160 (some 182)) = d4254 p := by
  change (if p 49 then d759 (change p 160 (some 182)) else d741 (change p 160 (some 182))) = d4254 p
  rw [sub3625, sub3577]
  rfl
theorem sub3627 (p : Pattern) : d6 (change p 160 (some 182)) = d6 p := by
  rfl
theorem sub3628 (p : Pattern) : d34 (change p 160 (some 182)) = d34 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d6 (change p 160 (some 182))) = d34 p
  rw [sub3498, sub3627]
  rfl
theorem sub3629 (p : Pattern) : d35 (change p 160 (some 182)) = d35 p := by
  change (if p 246 then d34 (change p 160 (some 182)) else d6 (change p 160 (some 182))) = d35 p
  rw [sub3628, sub3627]
  rfl
theorem sub3630 (p : Pattern) : d36 (change p 160 (some 182)) = d36 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d35 (change p 160 (some 182))) = d36 p
  rw [sub3498, sub3629]
  rfl
theorem sub3631 (p : Pattern) : d78 (change p 160 (some 182)) = d36 p := by
  change d36 (change p 160 (some 182)) = d36 p
  exact sub3630 p
theorem sub3632 (p : Pattern) : d79 (change p 160 (some 182)) = d4255 p := by
  change (if p 163 then d78 (change p 160 (some 182)) else d53 (change p 160 (some 182))) = d4255 p
  rw [sub3631, sub3523]
  rfl
theorem sub3633 (p : Pattern) : d188 (change p 160 (some 182)) = d4256 p := by
  change (if p 162 then d79 (change p 160 (some 182)) else d16 (change p 160 (some 182))) = d4256 p
  rw [sub3632, sub3502]
  rfl
theorem sub3634 (p : Pattern) : d80 (change p 160 (some 182)) = d4257 p := by
  change (if p 162 then d63 (change p 160 (some 182)) else d79 (change p 160 (some 182))) = d4257 p
  rw [sub3538, sub3632]
  rfl
theorem sub3635 (p : Pattern) : d189 (change p 160 (some 182)) = d4258 p := by
  change (if p 161 then d80 (change p 160 (some 182)) else d188 (change p 160 (some 182))) = d4258 p
  rw [sub3634, sub3633]
  rfl
theorem sub3636 (p : Pattern) : d761 (change p 160 (some 182)) = d4258 p := by
  change d189 (change p 160 (some 182)) = d4258 p
  exact sub3635 p
theorem sub3637 (p : Pattern) : d198 (change p 160 (some 182)) = d4259 p := by
  change (if p 163 then d62 (change p 160 (some 182)) else d20 (change p 160 (some 182))) = d4259 p
  rw [sub3537, sub3507]
  rfl
theorem sub3638 (p : Pattern) : d199 (change p 160 (some 182)) = d4260 p := by
  change (if p 162 then d198 (change p 160 (some 182)) else d53 (change p 160 (some 182))) = d4260 p
  rw [sub3637, sub3523]
  rfl
theorem sub3639 (p : Pattern) : d83 (change p 160 (some 182)) = d4261 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d78 (change p 160 (some 182))) = d4261 p
  rw [sub3498, sub3631]
  rfl
theorem sub3640 (p : Pattern) : d84 (change p 160 (some 182)) = d4262 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d83 (change p 160 (some 182))) = d4262 p
  rw [sub3498, sub3639]
  rfl
theorem sub3641 (p : Pattern) : d200 (change p 160 (some 182)) = d4263 p := by
  change (if p 161 then d84 (change p 160 (some 182)) else d199 (change p 160 (some 182))) = d4263 p
  rw [sub3640, sub3638]
  rfl
theorem sub3642 (p : Pattern) : d762 (change p 160 (some 182)) = d4263 p := by
  change d200 (change p 160 (some 182)) = d4263 p
  exact sub3641 p
theorem sub3643 (p : Pattern) : d763 (change p 160 (some 182)) = d4264 p := by
  change (if p 141 then d762 (change p 160 (some 182)) else d761 (change p 160 (some 182))) = d4264 p
  rw [sub3642, sub3636]
  rfl
theorem sub3644 (p : Pattern) : d764 (change p 160 (some 182)) = d4265 p := by
  change (if p 138 then d763 (change p 160 (some 182)) else d718 (change p 160 (some 182))) = d4265 p
  rw [sub3643, sub3548]
  rfl
theorem sub3645 (p : Pattern) : d765 (change p 160 (some 182)) = d4266 p := by
  change (if p 138 then d12 (change p 160 (some 182)) else d763 (change p 160 (some 182))) = d4266 p
  rw [sub3498, sub3643]
  rfl
theorem sub3646 (p : Pattern) : d766 (change p 160 (some 182)) = d4267 p := by
  change (if p 116 then d765 (change p 160 (some 182)) else d764 (change p 160 (some 182))) = d4267 p
  rw [sub3645, sub3644]
  rfl
theorem sub3647 (p : Pattern) : d767 (change p 160 (some 182)) = d4268 p := by
  change (if p 115 then d766 (change p 160 (some 182)) else d737 (change p 160 (some 182))) = d4268 p
  rw [sub3646, sub3573]
  rfl
theorem sub3648 (p : Pattern) : d768 (change p 160 (some 182)) = d4269 p := by
  change (if p 71 then d767 (change p 160 (some 182)) else d731 (change p 160 (some 182))) = d4269 p
  rw [sub3647, sub3567]
  rfl
theorem sub3649 (p : Pattern) : d211 (change p 160 (some 182)) = d4270 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d109 (change p 160 (some 182))) = d4270 p
  rw [sub3498, sub3587]
  rfl
theorem sub3650 (p : Pattern) : d212 (change p 160 (some 182)) = d4271 p := by
  change (if p 162 then d211 (change p 160 (some 182)) else d133 (change p 160 (some 182))) = d4271 p
  rw [sub3649, sub3599]
  rfl
theorem sub3651 (p : Pattern) : d213 (change p 160 (some 182)) = d4272 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d211 (change p 160 (some 182))) = d4272 p
  rw [sub3498, sub3649]
  rfl
theorem sub3652 (p : Pattern) : d214 (change p 160 (some 182)) = d4273 p := by
  change (if p 161 then d213 (change p 160 (some 182)) else d212 (change p 160 (some 182))) = d4273 p
  rw [sub3651, sub3650]
  rfl
theorem sub3653 (p : Pattern) : d769 (change p 160 (some 182)) = d4273 p := by
  change d214 (change p 160 (some 182)) = d4273 p
  exact sub3652 p
theorem sub3654 (p : Pattern) : d770 (change p 160 (some 182)) = d4274 p := by
  change (if p 141 then d769 (change p 160 (some 182)) else d742 (change p 160 (some 182))) = d4274 p
  rw [sub3653, sub3593]
  rfl
theorem sub3655 (p : Pattern) : d771 (change p 160 (some 182)) = d4273 p := by
  change d214 (change p 160 (some 182)) = d4273 p
  exact sub3652 p
theorem sub3656 (p : Pattern) : d772 (change p 160 (some 182)) = d4274 p := by
  change (if p 141 then d771 (change p 160 (some 182)) else d745 (change p 160 (some 182))) = d4274 p
  rw [sub3655, sub3607]
  rfl
theorem sub3657 (p : Pattern) : d773 (change p 160 (some 182)) = d4274 p := by
  change (if p 138 then d772 (change p 160 (some 182)) else d770 (change p 160 (some 182))) = d4274 p
  rw [sub3656, sub3654]
  simp only [ite_self]
theorem sub3658 (p : Pattern) : d774 (change p 160 (some 182)) = d4274 p := by
  change (if p 141 then d771 (change p 160 (some 182)) else d749 (change p 160 (some 182))) = d4274 p
  rw [sub3655, sub3611]
  rfl
theorem sub3659 (p : Pattern) : d775 (change p 160 (some 182)) = d4275 p := by
  change (if p 138 then d162 (change p 160 (some 182)) else d774 (change p 160 (some 182))) = d4275 p
  rw [sub3616, sub3658]
  rfl
theorem sub3660 (p : Pattern) : d776 (change p 160 (some 182)) = d4276 p := by
  change (if p 116 then d775 (change p 160 (some 182)) else d773 (change p 160 (some 182))) = d4276 p
  rw [sub3659, sub3657]
  rfl
theorem sub3661 (p : Pattern) : d777 (change p 160 (some 182)) = d4274 p := by
  change (if p 141 then d771 (change p 160 (some 182)) else d753 (change p 160 (some 182))) = d4274 p
  rw [sub3655, sub3619]
  rfl
theorem sub3662 (p : Pattern) : d241 (change p 160 (some 182)) = d4277 p := by
  change (if p 163 then d62 (change p 160 (some 182)) else d132 (change p 160 (some 182))) = d4277 p
  rw [sub3537, sub3598]
  rfl
theorem sub3663 (p : Pattern) : d242 (change p 160 (some 182)) = d4278 p := by
  change (if p 162 then d241 (change p 160 (some 182)) else d105 (change p 160 (some 182))) = d4278 p
  rw [sub3662, sub3582]
  rfl
theorem sub3664 (p : Pattern) : d243 (change p 160 (some 182)) = d4279 p := by
  change (if p 161 then d137 (change p 160 (some 182)) else d242 (change p 160 (some 182))) = d4279 p
  rw [sub3603, sub3663]
  rfl
theorem sub3665 (p : Pattern) : d778 (change p 160 (some 182)) = d4279 p := by
  change d243 (change p 160 (some 182)) = d4279 p
  exact sub3664 p
theorem sub3666 (p : Pattern) : d245 (change p 160 (some 182)) = d4280 p := by
  change (if p 162 then d211 (change p 160 (some 182)) else d132 (change p 160 (some 182))) = d4280 p
  rw [sub3649, sub3598]
  rfl
theorem sub3667 (p : Pattern) : d7 (change p 160 (some 182)) = d7 p := by
  rfl
theorem sub3668 (p : Pattern) : d119 (change p 160 (some 182)) = d119 p := by
  change (if p 247 then d12 (change p 160 (some 182)) else d7 (change p 160 (some 182))) = d119 p
  rw [sub3498, sub3667]
  rfl
theorem sub3669 (p : Pattern) : d120 (change p 160 (some 182)) = d120 p := by
  change (if p 246 then d119 (change p 160 (some 182)) else d7 (change p 160 (some 182))) = d120 p
  rw [sub3668, sub3667]
  rfl
theorem sub3670 (p : Pattern) : d121 (change p 160 (some 182)) = d121 p := by
  change (if p 204 then d12 (change p 160 (some 182)) else d120 (change p 160 (some 182))) = d121 p
  rw [sub3498, sub3669]
  rfl
theorem sub3671 (p : Pattern) : d148 (change p 160 (some 182)) = d121 p := by
  change d121 (change p 160 (some 182)) = d121 p
  exact sub3670 p
theorem sub3672 (p : Pattern) : d153 (change p 160 (some 182)) = d4281 p := by
  change (if p 163 then d12 (change p 160 (some 182)) else d148 (change p 160 (some 182))) = d4281 p
  rw [sub3498, sub3671]
  rfl
theorem sub3673 (p : Pattern) : d154 (change p 160 (some 182)) = d4282 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d153 (change p 160 (some 182))) = d4282 p
  rw [sub3498, sub3672]
  rfl
theorem sub3674 (p : Pattern) : d246 (change p 160 (some 182)) = d4283 p := by
  change (if p 161 then d154 (change p 160 (some 182)) else d245 (change p 160 (some 182))) = d4283 p
  rw [sub3673, sub3666]
  rfl
theorem sub3675 (p : Pattern) : d779 (change p 160 (some 182)) = d4283 p := by
  change d246 (change p 160 (some 182)) = d4283 p
  exact sub3674 p
theorem sub3676 (p : Pattern) : d780 (change p 160 (some 182)) = d4284 p := by
  change (if p 141 then d779 (change p 160 (some 182)) else d778 (change p 160 (some 182))) = d4284 p
  rw [sub3675, sub3665]
  rfl
theorem sub3677 (p : Pattern) : d781 (change p 160 (some 182)) = d4285 p := by
  change (if p 138 then d780 (change p 160 (some 182)) else d777 (change p 160 (some 182))) = d4285 p
  rw [sub3676, sub3661]
  rfl
theorem sub3678 (p : Pattern) : d252 (change p 160 (some 182)) = d4286 p := by
  change (if p 163 then d26 (change p 160 (some 182)) else d132 (change p 160 (some 182))) = d4286 p
  rw [sub3514, sub3598]
  rfl
theorem sub3679 (p : Pattern) : d253 (change p 160 (some 182)) = d4287 p := by
  change (if p 162 then d252 (change p 160 (some 182)) else d105 (change p 160 (some 182))) = d4287 p
  rw [sub3678, sub3582]
  rfl
theorem sub3680 (p : Pattern) : d254 (change p 160 (some 182)) = d4288 p := by
  change (if p 163 then d26 (change p 160 (some 182)) else d109 (change p 160 (some 182))) = d4288 p
  rw [sub3514, sub3587]
  rfl
theorem sub3681 (p : Pattern) : d255 (change p 160 (some 182)) = d4289 p := by
  change (if p 162 then d12 (change p 160 (some 182)) else d254 (change p 160 (some 182))) = d4289 p
  rw [sub3498, sub3680]
  rfl
theorem sub3682 (p : Pattern) : d256 (change p 160 (some 182)) = d4290 p := by
  change (if p 161 then d255 (change p 160 (some 182)) else d253 (change p 160 (some 182))) = d4290 p
  rw [sub3681, sub3679]
  rfl
theorem sub3683 (p : Pattern) : d782 (change p 160 (some 182)) = d4290 p := by
  change d256 (change p 160 (some 182)) = d4290 p
  exact sub3682 p
theorem sub3684 (p : Pattern) : d783 (change p 160 (some 182)) = d4291 p := by
  change (if p 141 then d779 (change p 160 (some 182)) else d782 (change p 160 (some 182))) = d4291 p
  rw [sub3675, sub3683]
  rfl
theorem sub3685 (p : Pattern) : d784 (change p 160 (some 182)) = d4292 p := by
  change (if p 138 then d12 (change p 160 (some 182)) else d783 (change p 160 (some 182))) = d4292 p
  rw [sub3498, sub3684]
  rfl
theorem sub3686 (p : Pattern) : d785 (change p 160 (some 182)) = d4293 p := by
  change (if p 116 then d784 (change p 160 (some 182)) else d781 (change p 160 (some 182))) = d4293 p
  rw [sub3685, sub3677]
  rfl
theorem sub3687 (p : Pattern) : d786 (change p 160 (some 182)) = d4294 p := by
  change (if p 115 then d785 (change p 160 (some 182)) else d776 (change p 160 (some 182))) = d4294 p
  rw [sub3686, sub3660]
  rfl
theorem sub3688 (p : Pattern) : d787 (change p 160 (some 182)) = d4295 p := by
  change (if p 71 then d786 (change p 160 (some 182)) else d731 (change p 160 (some 182))) = d4295 p
  rw [sub3687, sub3567]
  rfl
theorem sub3689 (p : Pattern) : d788 (change p 160 (some 182)) = d4296 p := by
  change (if p 49 then d787 (change p 160 (some 182)) else d768 (change p 160 (some 182))) = d4296 p
  rw [sub3688, sub3648]
  rfl
theorem sub3690 (p : Pattern) : d789 (change p 160 (some 182)) = d4297 p := by
  change (if p 48 then d788 (change p 160 (some 182)) else d760 (change p 160 (some 182))) = d4297 p
  rw [sub3689, sub3626]
  rfl
theorem sub3691 (p : Pattern) : d0 (change p 163 none) = d0 p := by
  rfl
theorem sub3692 (p : Pattern) : d12 (change p 163 none) = d12 p := by
  rfl
theorem sub3693 (p : Pattern) : d13 (change p 163 none) = d13 p := by
  change (if p 247 then d12 (change p 163 none) else d0 (change p 163 none)) = d13 p
  rw [sub3692, sub3691]
  rfl
theorem sub3694 (p : Pattern) : d14 (change p 163 none) = d14 p := by
  change (if p 246 then d13 (change p 163 none) else d0 (change p 163 none)) = d14 p
  rw [sub3693, sub3691]
  rfl
theorem sub3695 (p : Pattern) : d15 (change p 163 none) = d15 p := by
  change (if p 204 then d12 (change p 163 none) else d14 (change p 163 none)) = d15 p
  rw [sub3692, sub3694]
  rfl
theorem sub3696 (p : Pattern) : d16 (change p 163 none) = d16 p := by
  change (if p 182 then d15 (change p 163 none) else d14 (change p 163 none)) = d16 p
  rw [sub3695, sub3694]
  rfl
theorem sub3697 (p : Pattern) : d1151 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3698 (p : Pattern) : d1152 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3699 (p : Pattern) : d1153 (change p 163 none) = d16 p := by
  change (if p 162 then d1152 (change p 163 none) else d1151 (change p 163 none)) = d16 p
  rw [sub3698, sub3697]
  simp only [ite_self]
theorem sub3700 (p : Pattern) : d1154 (change p 163 none) = d16 p := by
  change d16 (change p 163 none) = d16 p
  exact sub3696 p
theorem sub3701 (p : Pattern) : d9 (change p 163 none) = d9 p := by
  rfl
theorem sub3702 (p : Pattern) : d23 (change p 163 none) = d23 p := by
  change (if p 247 then d12 (change p 163 none) else d9 (change p 163 none)) = d23 p
  rw [sub3692, sub3701]
  rfl
theorem sub3703 (p : Pattern) : d24 (change p 163 none) = d24 p := by
  change (if p 246 then d23 (change p 163 none) else d9 (change p 163 none)) = d24 p
  rw [sub3702, sub3701]
  rfl
theorem sub3704 (p : Pattern) : d25 (change p 163 none) = d25 p := by
  change (if p 204 then d12 (change p 163 none) else d24 (change p 163 none)) = d25 p
  rw [sub3692, sub3703]
  rfl
theorem sub3705 (p : Pattern) : d26 (change p 163 none) = d26 p := by
  change (if p 182 then d25 (change p 163 none) else d24 (change p 163 none)) = d26 p
  rw [sub3704, sub3703]
  rfl
theorem sub3706 (p : Pattern) : d27 (change p 163 none) = d26 p := by
  change d26 (change p 163 none) = d26 p
  exact sub3705 p
theorem sub3707 (p : Pattern) : d1155 (change p 163 none) = d4305 p := by
  change (if p 162 then d27 (change p 163 none) else d1154 (change p 163 none)) = d4305 p
  rw [sub3706, sub3700]
  rfl
theorem sub3708 (p : Pattern) : d1156 (change p 163 none) = d4306 p := by
  change (if p 161 then d1155 (change p 163 none) else d1153 (change p 163 none)) = d4306 p
  rw [sub3707, sub3699]
  rfl
theorem sub3709 (p : Pattern) : d2 (change p 163 none) = d2 p := by
  rfl
theorem sub3710 (p : Pattern) : d30 (change p 163 none) = d30 p := by
  change (if p 247 then d12 (change p 163 none) else d2 (change p 163 none)) = d30 p
  rw [sub3692, sub3709]
  rfl
theorem sub3711 (p : Pattern) : d31 (change p 163 none) = d31 p := by
  change (if p 246 then d30 (change p 163 none) else d2 (change p 163 none)) = d31 p
  rw [sub3710, sub3709]
  rfl
theorem sub3712 (p : Pattern) : d32 (change p 163 none) = d32 p := by
  change (if p 204 then d12 (change p 163 none) else d31 (change p 163 none)) = d32 p
  rw [sub3692, sub3711]
  rfl
theorem sub3713 (p : Pattern) : d33 (change p 163 none) = d33 p := by
  change (if p 182 then d32 (change p 163 none) else d14 (change p 163 none)) = d33 p
  rw [sub3712, sub3694]
  rfl
theorem sub3714 (p : Pattern) : d1157 (change p 163 none) = d33 p := by
  change d33 (change p 163 none) = d33 p
  exact sub3713 p
theorem sub3715 (p : Pattern) : d11 (change p 163 none) = d11 p := by
  rfl
theorem sub3716 (p : Pattern) : d39 (change p 163 none) = d39 p := by
  change (if p 247 then d12 (change p 163 none) else d11 (change p 163 none)) = d39 p
  rw [sub3692, sub3715]
  rfl
theorem sub3717 (p : Pattern) : d40 (change p 163 none) = d40 p := by
  change (if p 246 then d39 (change p 163 none) else d11 (change p 163 none)) = d40 p
  rw [sub3716, sub3715]
  rfl
theorem sub3718 (p : Pattern) : d41 (change p 163 none) = d41 p := by
  change (if p 204 then d12 (change p 163 none) else d40 (change p 163 none)) = d41 p
  rw [sub3692, sub3717]
  rfl
theorem sub3719 (p : Pattern) : d42 (change p 163 none) = d42 p := by
  change (if p 182 then d41 (change p 163 none) else d14 (change p 163 none)) = d42 p
  rw [sub3718, sub3694]
  rfl
end NetHack.Sokoban22Refined85
