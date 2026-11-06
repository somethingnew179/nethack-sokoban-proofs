/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13200 (p : Pattern) : d3600 (change p 247 (some 246)) = d7289 p := by
  change (if p 182 then d3599 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7289 p
  rw [sub13199, sub13177]
  rfl
theorem sub13201 (p : Pattern) : d3601 (change p 247 (some 246)) = d10 p := by
  change d57 (change p 247 (some 246)) = d10 p
  exact sub13189 p
theorem sub13202 (p : Pattern) : d3602 (change p 247 (some 246)) = d7290 p := by
  change (if p 225 then d3601 (change p 247 (some 246)) else d17 (change p 247 (some 246))) = d7290 p
  rw [sub13201, sub13125]
  rfl
theorem sub13203 (p : Pattern) : d339 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13204 (p : Pattern) : d3603 (change p 247 (some 246)) = d7291 p := by
  change (if p 225 then d339 (change p 247 (some 246)) else d3555 (change p 247 (some 246))) = d7291 p
  rw [sub13203, sub13143]
  rfl
theorem sub13205 (p : Pattern) : d3604 (change p 247 (some 246)) = d7292 p := by
  change (if p 224 then d3603 (change p 247 (some 246)) else d3602 (change p 247 (some 246))) = d7292 p
  rw [sub13204, sub13202]
  rfl
theorem sub13206 (p : Pattern) : d3605 (change p 247 (some 246)) = d7293 p := by
  change (if p 204 then d3604 (change p 247 (some 246)) else d17 (change p 247 (some 246))) = d7293 p
  rw [sub13205, sub13125]
  rfl
theorem sub13207 (p : Pattern) : d3606 (change p 247 (some 246)) = d7294 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3605 (change p 247 (some 246))) = d7294 p
  rw [sub13135, sub13206]
  rfl
theorem sub13208 (p : Pattern) : d3607 (change p 247 (some 246)) = d7295 p := by
  change (if p 163 then d3606 (change p 247 (some 246)) else d3600 (change p 247 (some 246))) = d7295 p
  rw [sub13207, sub13200]
  rfl
theorem sub13209 (p : Pattern) : d3608 (change p 247 (some 246)) = d7296 p := by
  change (if p 162 then d3607 (change p 247 (some 246)) else d3596 (change p 247 (some 246))) = d7296 p
  rw [sub13208, sub13195]
  rfl
theorem sub13210 (p : Pattern) : d3609 (change p 247 (some 246)) = d7297 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7297 p
  rw [sub13135, sub13177]
  rfl
theorem sub13211 (p : Pattern) : d3610 (change p 247 (some 246)) = d7298 p := by
  change (if p 163 then d3606 (change p 247 (some 246)) else d3609 (change p 247 (some 246))) = d7298 p
  rw [sub13207, sub13210]
  rfl
theorem sub13212 (p : Pattern) : d3611 (change p 247 (some 246)) = d7299 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3568 (change p 247 (some 246))) = d7299 p
  rw [sub13135, sub13161]
  rfl
theorem sub13213 (p : Pattern) : d3612 (change p 247 (some 246)) = d7300 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3611 (change p 247 (some 246))) = d7300 p
  rw [sub13135, sub13212]
  rfl
theorem sub13214 (p : Pattern) : d3613 (change p 247 (some 246)) = d7301 p := by
  change (if p 162 then d3612 (change p 247 (some 246)) else d3610 (change p 247 (some 246))) = d7301 p
  rw [sub13213, sub13211]
  rfl
theorem sub13215 (p : Pattern) : d3614 (change p 247 (some 246)) = d7302 p := by
  change (if p 161 then d3613 (change p 247 (some 246)) else d3608 (change p 247 (some 246))) = d7302 p
  rw [sub13214, sub13209]
  rfl
theorem sub13216 (p : Pattern) : d3615 (change p 247 (some 246)) = d7303 p := by
  change (if p 160 then d3614 (change p 247 (some 246)) else d3576 (change p 247 (some 246))) = d7303 p
  rw [sub13215, sub13171]
  rfl
theorem sub13217 (p : Pattern) : d3616 (change p 247 (some 246)) = d0 p := by
  change d13 (change p 247 (some 246)) = d0 p
  exact sub13120 p
theorem sub13218 (p : Pattern) : d3617 (change p 247 (some 246)) = d0 p := by
  change (if p 225 then d13 (change p 247 (some 246)) else d3616 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13217]
  simp only [ite_self]
theorem sub13219 (p : Pattern) : d3618 (change p 247 (some 246)) = d0 p := by
  change (if p 224 then d13 (change p 247 (some 246)) else d3617 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13218]
  simp only [ite_self]
theorem sub13220 (p : Pattern) : d3619 (change p 247 (some 246)) = d7247 p := by
  change (if p 204 then d3545 (change p 247 (some 246)) else d3618 (change p 247 (some 246))) = d7247 p
  rw [sub13128, sub13219]
  rfl
theorem sub13221 (p : Pattern) : d3620 (change p 247 (some 246)) = d7251 p := by
  change (if p 182 then d3550 (change p 247 (some 246)) else d3619 (change p 247 (some 246))) = d7251 p
  rw [sub13136, sub13220]
  rfl
theorem sub13222 (p : Pattern) : d3621 (change p 247 (some 246)) = d7304 p := by
  change (if p 225 then d3585 (change p 247 (some 246)) else d30 (change p 247 (some 246))) = d7304 p
  rw [sub13180, sub13131]
  rfl
theorem sub13223 (p : Pattern) : d3622 (change p 247 (some 246)) = d7305 p := by
  change (if p 224 then d3585 (change p 247 (some 246)) else d3621 (change p 247 (some 246))) = d7305 p
  rw [sub13180, sub13222]
  rfl
theorem sub13224 (p : Pattern) : d3623 (change p 247 (some 246)) = d7306 p := by
  change (if p 204 then d3622 (change p 247 (some 246)) else d30 (change p 247 (some 246))) = d7306 p
  rw [sub13223, sub13131]
  rfl
theorem sub13225 (p : Pattern) : d3624 (change p 247 (some 246)) = d4 p := by
  change d17 (change p 247 (some 246)) = d4 p
  exact sub13125 p
theorem sub13226 (p : Pattern) : d3625 (change p 247 (some 246)) = d7307 p := by
  change (if p 225 then d3624 (change p 247 (some 246)) else d30 (change p 247 (some 246))) = d7307 p
  rw [sub13225, sub13131]
  rfl
theorem sub13227 (p : Pattern) : d3626 (change p 247 (some 246)) = d7308 p := by
  change (if p 224 then d3624 (change p 247 (some 246)) else d3625 (change p 247 (some 246))) = d7308 p
  rw [sub13225, sub13226]
  rfl
theorem sub13228 (p : Pattern) : d3627 (change p 247 (some 246)) = d7309 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3626 (change p 247 (some 246))) = d7309 p
  rw [sub13135, sub13227]
  rfl
theorem sub13229 (p : Pattern) : d3628 (change p 247 (some 246)) = d7310 p := by
  change (if p 182 then d3627 (change p 247 (some 246)) else d3623 (change p 247 (some 246))) = d7310 p
  rw [sub13228, sub13224]
  rfl
theorem sub13230 (p : Pattern) : d3629 (change p 247 (some 246)) = d7311 p := by
  change (if p 163 then d3628 (change p 247 (some 246)) else d3620 (change p 247 (some 246))) = d7311 p
  rw [sub13229, sub13221]
  rfl
theorem sub13231 (p : Pattern) : d3630 (change p 247 (some 246)) = d7312 p := by
  change (if p 163 then d3573 (change p 247 (some 246)) else d3563 (change p 247 (some 246))) = d7312 p
  rw [sub13168, sub13153]
  rfl
theorem sub13232 (p : Pattern) : d3631 (change p 247 (some 246)) = d7313 p := by
  change (if p 162 then d3630 (change p 247 (some 246)) else d3629 (change p 247 (some 246))) = d7313 p
  rw [sub13231, sub13230]
  rfl
theorem sub13233 (p : Pattern) : d329 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13234 (p : Pattern) : d3632 (change p 247 (some 246)) = d7281 p := by
  change (if p 225 then d329 (change p 247 (some 246)) else d57 (change p 247 (some 246))) = d7281 p
  rw [sub13233, sub13189]
  rfl
theorem sub13235 (p : Pattern) : d3633 (change p 247 (some 246)) = d7314 p := by
  change (if p 224 then d329 (change p 247 (some 246)) else d3632 (change p 247 (some 246))) = d7314 p
  rw [sub13233, sub13234]
  rfl
theorem sub13236 (p : Pattern) : d3634 (change p 247 (some 246)) = d7315 p := by
  change (if p 204 then d3633 (change p 247 (some 246)) else d57 (change p 247 (some 246))) = d7315 p
  rw [sub13235, sub13189]
  rfl
theorem sub13237 (p : Pattern) : d3635 (change p 247 (some 246)) = d7316 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3633 (change p 247 (some 246))) = d7316 p
  rw [sub13135, sub13235]
  rfl
theorem sub13238 (p : Pattern) : d3636 (change p 247 (some 246)) = d7317 p := by
  change (if p 182 then d3635 (change p 247 (some 246)) else d3634 (change p 247 (some 246))) = d7317 p
  rw [sub13237, sub13236]
  rfl
theorem sub13239 (p : Pattern) : d3637 (change p 247 (some 246)) = d7318 p := by
  change (if p 163 then d3636 (change p 247 (some 246)) else d3563 (change p 247 (some 246))) = d7318 p
  rw [sub13238, sub13153]
  rfl
theorem sub13240 (p : Pattern) : d3638 (change p 247 (some 246)) = d7319 p := by
  change (if p 204 then d3598 (change p 247 (some 246)) else d39 (change p 247 (some 246))) = d7319 p
  rw [sub13198, sub13163]
  rfl
theorem sub13241 (p : Pattern) : d3639 (change p 247 (some 246)) = d7320 p := by
  change (if p 182 then d3599 (change p 247 (some 246)) else d3638 (change p 247 (some 246))) = d7320 p
  rw [sub13199, sub13240]
  rfl
theorem sub13242 (p : Pattern) : d3640 (change p 247 (some 246)) = d7321 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3639 (change p 247 (some 246))) = d7321 p
  rw [sub13135, sub13241]
  rfl
theorem sub13243 (p : Pattern) : d3641 (change p 247 (some 246)) = d7322 p := by
  change (if p 162 then d3640 (change p 247 (some 246)) else d3637 (change p 247 (some 246))) = d7322 p
  rw [sub13242, sub13239]
  rfl
theorem sub13244 (p : Pattern) : d3642 (change p 247 (some 246)) = d7323 p := by
  change (if p 161 then d3641 (change p 247 (some 246)) else d3631 (change p 247 (some 246))) = d7323 p
  rw [sub13243, sub13232]
  rfl
theorem sub13245 (p : Pattern) : d3643 (change p 247 (some 246)) = d7324 p := by
  change (if p 204 then d3587 (change p 247 (some 246)) else d30 (change p 247 (some 246))) = d7324 p
  rw [sub13183, sub13131]
  rfl
theorem sub13246 (p : Pattern) : d3644 (change p 247 (some 246)) = d7325 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3643 (change p 247 (some 246))) = d7325 p
  rw [sub13135, sub13245]
  rfl
theorem sub13247 (p : Pattern) : d3645 (change p 247 (some 246)) = d7326 p := by
  change (if p 163 then d3644 (change p 247 (some 246)) else d3595 (change p 247 (some 246))) = d7326 p
  rw [sub13246, sub13194]
  rfl
theorem sub13248 (p : Pattern) : d3646 (change p 247 (some 246)) = d7327 p := by
  change (if p 163 then d3611 (change p 247 (some 246)) else d3606 (change p 247 (some 246))) = d7327 p
  rw [sub13212, sub13207]
  rfl
theorem sub13249 (p : Pattern) : d3647 (change p 247 (some 246)) = d7328 p := by
  change (if p 162 then d3646 (change p 247 (some 246)) else d3645 (change p 247 (some 246))) = d7328 p
  rw [sub13248, sub13247]
  rfl
theorem sub13250 (p : Pattern) : d3648 (change p 247 (some 246)) = d7329 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3634 (change p 247 (some 246))) = d7329 p
  rw [sub13135, sub13236]
  rfl
theorem sub13251 (p : Pattern) : d3649 (change p 247 (some 246)) = d7330 p := by
  change (if p 163 then d3648 (change p 247 (some 246)) else d3606 (change p 247 (some 246))) = d7330 p
  rw [sub13250, sub13207]
  rfl
theorem sub13252 (p : Pattern) : d3650 (change p 247 (some 246)) = d7331 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3638 (change p 247 (some 246))) = d7331 p
  rw [sub13135, sub13240]
  rfl
theorem sub13253 (p : Pattern) : d3651 (change p 247 (some 246)) = d7332 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3650 (change p 247 (some 246))) = d7332 p
  rw [sub13135, sub13252]
  rfl
theorem sub13254 (p : Pattern) : d3652 (change p 247 (some 246)) = d7333 p := by
  change (if p 162 then d3651 (change p 247 (some 246)) else d3649 (change p 247 (some 246))) = d7333 p
  rw [sub13253, sub13251]
  rfl
theorem sub13255 (p : Pattern) : d3653 (change p 247 (some 246)) = d7334 p := by
  change (if p 161 then d3652 (change p 247 (some 246)) else d3647 (change p 247 (some 246))) = d7334 p
  rw [sub13254, sub13249]
  rfl
theorem sub13256 (p : Pattern) : d3654 (change p 247 (some 246)) = d7335 p := by
  change (if p 160 then d3653 (change p 247 (some 246)) else d3642 (change p 247 (some 246))) = d7335 p
  rw [sub13255, sub13244]
  rfl
theorem sub13257 (p : Pattern) : d3655 (change p 247 (some 246)) = d7336 p := by
  change (if p 141 then d3654 (change p 247 (some 246)) else d3615 (change p 247 (some 246))) = d7336 p
  rw [sub13256, sub13216]
  rfl
theorem sub13258 (p : Pattern) : d3656 (change p 247 (some 246)) = d7255 p := by
  change (if p 225 then d3577 (change p 247 (some 246)) else d3543 (change p 247 (some 246))) = d7255 p
  rw [sub13172, sub13126]
  rfl
theorem sub13259 (p : Pattern) : d3657 (change p 247 (some 246)) = d7337 p := by
  change (if p 224 then d3656 (change p 247 (some 246)) else d3578 (change p 247 (some 246))) = d7337 p
  rw [sub13258, sub13173]
  rfl
theorem sub13260 (p : Pattern) : d3658 (change p 247 (some 246)) = d7338 p := by
  change (if p 204 then d3657 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7338 p
  rw [sub13259, sub13120]
  rfl
theorem sub13261 (p : Pattern) : d3659 (change p 247 (some 246)) = d7339 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3545 (change p 247 (some 246))) = d7339 p
  rw [sub13135, sub13128]
  rfl
theorem sub13262 (p : Pattern) : d3660 (change p 247 (some 246)) = d7340 p := by
  change (if p 182 then d3659 (change p 247 (some 246)) else d3658 (change p 247 (some 246))) = d7340 p
  rw [sub13261, sub13260]
  rfl
theorem sub13263 (p : Pattern) : d3661 (change p 247 (some 246)) = d8 p := by
  change d190 (change p 247 (some 246)) = d8 p
  exact sub13142 p
theorem sub13264 (p : Pattern) : d3662 (change p 247 (some 246)) = d7252 p := by
  change (if p 225 then d3661 (change p 247 (some 246)) else d3543 (change p 247 (some 246))) = d7252 p
  rw [sub13263, sub13126]
  rfl
theorem sub13265 (p : Pattern) : d3663 (change p 247 (some 246)) = d7341 p := by
  change (if p 224 then d3662 (change p 247 (some 246)) else d3578 (change p 247 (some 246))) = d7341 p
  rw [sub13264, sub13173]
  rfl
theorem sub13266 (p : Pattern) : d3664 (change p 247 (some 246)) = d7342 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3663 (change p 247 (some 246))) = d7342 p
  rw [sub13135, sub13265]
  rfl
theorem sub13267 (p : Pattern) : d3665 (change p 247 (some 246)) = d7343 p := by
  change (if p 182 then d3664 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7343 p
  rw [sub13266, sub13177]
  rfl
theorem sub13268 (p : Pattern) : d3666 (change p 247 (some 246)) = d7344 p := by
  change (if p 163 then d3665 (change p 247 (some 246)) else d3660 (change p 247 (some 246))) = d7344 p
  rw [sub13267, sub13262]
  rfl
theorem sub13269 (p : Pattern) : d3667 (change p 247 (some 246)) = d7345 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3581 (change p 247 (some 246))) = d7345 p
  rw [sub13135, sub13176]
  rfl
theorem sub13270 (p : Pattern) : d3668 (change p 247 (some 246)) = d7346 p := by
  change (if p 182 then d3667 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7346 p
  rw [sub13269, sub13177]
  rfl
theorem sub13271 (p : Pattern) : d3669 (change p 247 (some 246)) = d7347 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3604 (change p 247 (some 246))) = d7347 p
  rw [sub13135, sub13205]
  rfl
theorem sub13272 (p : Pattern) : d3670 (change p 247 (some 246)) = d7348 p := by
  change (if p 182 then d3669 (change p 247 (some 246)) else d3605 (change p 247 (some 246))) = d7348 p
  rw [sub13271, sub13206]
  rfl
theorem sub13273 (p : Pattern) : d3671 (change p 247 (some 246)) = d7349 p := by
  change (if p 163 then d3670 (change p 247 (some 246)) else d3668 (change p 247 (some 246))) = d7349 p
  rw [sub13272, sub13270]
  rfl
theorem sub13274 (p : Pattern) : d3672 (change p 247 (some 246)) = d7350 p := by
  change (if p 162 then d3671 (change p 247 (some 246)) else d3666 (change p 247 (some 246))) = d7350 p
  rw [sub13273, sub13268]
  rfl
theorem sub13275 (p : Pattern) : d3673 (change p 247 (some 246)) = d7351 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3567 (change p 247 (some 246))) = d7351 p
  rw [sub13135, sub13160]
  rfl
theorem sub13276 (p : Pattern) : d3674 (change p 247 (some 246)) = d7352 p := by
  change (if p 182 then d3673 (change p 247 (some 246)) else d3568 (change p 247 (some 246))) = d7352 p
  rw [sub13275, sub13161]
  rfl
theorem sub13277 (p : Pattern) : d3675 (change p 247 (some 246)) = d7353 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3674 (change p 247 (some 246))) = d7353 p
  rw [sub13135, sub13276]
  rfl
theorem sub13278 (p : Pattern) : d3676 (change p 247 (some 246)) = d7354 p := by
  change (if p 162 then d3675 (change p 247 (some 246)) else d3671 (change p 247 (some 246))) = d7354 p
  rw [sub13277, sub13273]
  rfl
theorem sub13279 (p : Pattern) : d3677 (change p 247 (some 246)) = d7355 p := by
  change (if p 161 then d3676 (change p 247 (some 246)) else d3672 (change p 247 (some 246))) = d7355 p
  rw [sub13278, sub13274]
  rfl
theorem sub13280 (p : Pattern) : d3678 (change p 247 (some 246)) = d7356 p := by
  change (if p 182 then d3588 (change p 247 (some 246)) else d3643 (change p 247 (some 246))) = d7356 p
  rw [sub13184, sub13245]
  rfl
theorem sub13281 (p : Pattern) : d3679 (change p 247 (some 246)) = d7357 p := by
  change (if p 204 then d3593 (change p 247 (some 246)) else d34 (change p 247 (some 246))) = d7357 p
  rw [sub13192, sub13148]
  rfl
theorem sub13282 (p : Pattern) : d3680 (change p 247 (some 246)) = d7358 p := by
  change (if p 182 then d3594 (change p 247 (some 246)) else d3679 (change p 247 (some 246))) = d7358 p
  rw [sub13193, sub13281]
  rfl
theorem sub13283 (p : Pattern) : d3681 (change p 247 (some 246)) = d7359 p := by
  change (if p 163 then d3680 (change p 247 (some 246)) else d3678 (change p 247 (some 246))) = d7359 p
  rw [sub13282, sub13280]
  rfl
theorem sub13284 (p : Pattern) : d3682 (change p 247 (some 246)) = d7360 p := by
  change (if p 162 then d3640 (change p 247 (some 246)) else d3681 (change p 247 (some 246))) = d7360 p
  rw [sub13242, sub13283]
  rfl
theorem sub13285 (p : Pattern) : d3683 (change p 247 (some 246)) = d7361 p := by
  change (if p 161 then d12 (change p 247 (some 246)) else d3682 (change p 247 (some 246))) = d7361 p
  rw [sub13135, sub13284]
  rfl
theorem sub13286 (p : Pattern) : d3684 (change p 247 (some 246)) = d7362 p := by
  change (if p 160 then d3683 (change p 247 (some 246)) else d3677 (change p 247 (some 246))) = d7362 p
  rw [sub13285, sub13279]
  rfl
theorem sub13287 (p : Pattern) : d3685 (change p 247 (some 246)) = d7363 p := by
  change (if p 163 then d3678 (change p 247 (some 246)) else d3665 (change p 247 (some 246))) = d7363 p
  rw [sub13280, sub13267]
  rfl
theorem sub13288 (p : Pattern) : d3686 (change p 247 (some 246)) = d7364 p := by
  change (if p 163 then d3674 (change p 247 (some 246)) else d3670 (change p 247 (some 246))) = d7364 p
  rw [sub13276, sub13272]
  rfl
theorem sub13289 (p : Pattern) : d3687 (change p 247 (some 246)) = d7365 p := by
  change (if p 162 then d3686 (change p 247 (some 246)) else d3685 (change p 247 (some 246))) = d7365 p
  rw [sub13288, sub13287]
  rfl
theorem sub13290 (p : Pattern) : d3688 (change p 247 (some 246)) = d7366 p := by
  change (if p 163 then d3636 (change p 247 (some 246)) else d3670 (change p 247 (some 246))) = d7366 p
  rw [sub13238, sub13272]
  rfl
theorem sub13291 (p : Pattern) : d3689 (change p 247 (some 246)) = d7367 p := by
  change (if p 162 then d3640 (change p 247 (some 246)) else d3688 (change p 247 (some 246))) = d7367 p
  rw [sub13242, sub13290]
  rfl
theorem sub13292 (p : Pattern) : d3690 (change p 247 (some 246)) = d7368 p := by
  change (if p 161 then d3689 (change p 247 (some 246)) else d3687 (change p 247 (some 246))) = d7368 p
  rw [sub13291, sub13289]
  rfl
theorem sub13293 (p : Pattern) : d3691 (change p 247 (some 246)) = d7369 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3680 (change p 247 (some 246))) = d7369 p
  rw [sub13135, sub13282]
  rfl
theorem sub13294 (p : Pattern) : d3692 (change p 247 (some 246)) = d7370 p := by
  change (if p 162 then d12 (change p 247 (some 246)) else d3691 (change p 247 (some 246))) = d7370 p
  rw [sub13135, sub13293]
  rfl
theorem sub13295 (p : Pattern) : d3693 (change p 247 (some 246)) = d7371 p := by
  change (if p 161 then d12 (change p 247 (some 246)) else d3692 (change p 247 (some 246))) = d7371 p
  rw [sub13135, sub13294]
  rfl
theorem sub13296 (p : Pattern) : d3694 (change p 247 (some 246)) = d7372 p := by
  change (if p 160 then d3693 (change p 247 (some 246)) else d3690 (change p 247 (some 246))) = d7372 p
  rw [sub13295, sub13292]
  rfl
theorem sub13297 (p : Pattern) : d3695 (change p 247 (some 246)) = d7373 p := by
  change (if p 141 then d3694 (change p 247 (some 246)) else d3684 (change p 247 (some 246))) = d7373 p
  rw [sub13296, sub13286]
  rfl
theorem sub13298 (p : Pattern) : d3696 (change p 247 (some 246)) = d7374 p := by
  change (if p 138 then d3695 (change p 247 (some 246)) else d3655 (change p 247 (some 246))) = d7374 p
  rw [sub13297, sub13257]
  rfl
theorem sub13299 (p : Pattern) : d3697 (change p 247 (some 246)) = d7375 p := by
  change (if p 163 then d3639 (change p 247 (some 246)) else d3674 (change p 247 (some 246))) = d7375 p
  rw [sub13241, sub13276]
  rfl
theorem sub13300 (p : Pattern) : d3698 (change p 247 (some 246)) = d7376 p := by
  change (if p 162 then d3640 (change p 247 (some 246)) else d3697 (change p 247 (some 246))) = d7376 p
  rw [sub13242, sub13299]
  rfl
theorem sub13301 (p : Pattern) : d3699 (change p 247 (some 246)) = d7377 p := by
  change (if p 162 then d12 (change p 247 (some 246)) else d3640 (change p 247 (some 246))) = d7377 p
  rw [sub13135, sub13242]
  rfl
theorem sub13302 (p : Pattern) : d3700 (change p 247 (some 246)) = d7378 p := by
  change (if p 161 then d3699 (change p 247 (some 246)) else d3698 (change p 247 (some 246))) = d7378 p
  rw [sub13301, sub13300]
  rfl
theorem sub13303 (p : Pattern) : d3701 (change p 247 (some 246)) = d7379 p := by
  change (if p 161 then d12 (change p 247 (some 246)) else d3699 (change p 247 (some 246))) = d7379 p
  rw [sub13135, sub13301]
  rfl
theorem sub13304 (p : Pattern) : d3702 (change p 247 (some 246)) = d7380 p := by
  change (if p 160 then d3701 (change p 247 (some 246)) else d3700 (change p 247 (some 246))) = d7380 p
  rw [sub13303, sub13302]
  rfl
theorem sub13305 (p : Pattern) : d3703 (change p 247 (some 246)) = d7381 p := by
  change (if p 160 then d12 (change p 247 (some 246)) else d3701 (change p 247 (some 246))) = d7381 p
  rw [sub13135, sub13303]
  rfl
theorem sub13306 (p : Pattern) : d3704 (change p 247 (some 246)) = d7382 p := by
  change (if p 141 then d3703 (change p 247 (some 246)) else d3702 (change p 247 (some 246))) = d7382 p
  rw [sub13305, sub13304]
  rfl
theorem sub13307 (p : Pattern) : d3705 (change p 247 (some 246)) = d7383 p := by
  change (if p 138 then d3704 (change p 247 (some 246)) else d3695 (change p 247 (some 246))) = d7383 p
  rw [sub13306, sub13297]
  rfl
theorem sub13308 (p : Pattern) : d3706 (change p 247 (some 246)) = d7384 p := by
  change (if p 116 then d3705 (change p 247 (some 246)) else d3696 (change p 247 (some 246))) = d7384 p
  rw [sub13307, sub13298]
  rfl
theorem sub13309 (p : Pattern) : d3707 (change p 247 (some 246)) = d7260 p := by
  change (if p 162 then d3564 (change p 247 (some 246)) else d3553 (change p 247 (some 246))) = d7260 p
  rw [sub13154, sub13139]
  rfl
theorem sub13310 (p : Pattern) : d3708 (change p 247 (some 246)) = d7270 p := by
  change (if p 161 then d3575 (change p 247 (some 246)) else d3707 (change p 247 (some 246))) = d7270 p
  rw [sub13170, sub13309]
  rfl
theorem sub13311 (p : Pattern) : d3709 (change p 247 (some 246)) = d7303 p := by
  change (if p 160 then d3614 (change p 247 (some 246)) else d3708 (change p 247 (some 246))) = d7303 p
  rw [sub13215, sub13310]
  rfl
theorem sub13312 (p : Pattern) : d3710 (change p 247 (some 246)) = d7311 p := by
  change (if p 163 then d3628 (change p 247 (some 246)) else d3553 (change p 247 (some 246))) = d7311 p
  rw [sub13229, sub13139]
  rfl
theorem sub13313 (p : Pattern) : d3711 (change p 247 (some 246)) = d7313 p := by
  change (if p 162 then d3630 (change p 247 (some 246)) else d3710 (change p 247 (some 246))) = d7313 p
  rw [sub13231, sub13312]
  rfl
theorem sub13314 (p : Pattern) : d3712 (change p 247 (some 246)) = d7323 p := by
  change (if p 161 then d3641 (change p 247 (some 246)) else d3711 (change p 247 (some 246))) = d7323 p
  rw [sub13243, sub13313]
  rfl
theorem sub13315 (p : Pattern) : d3713 (change p 247 (some 246)) = d7335 p := by
  change (if p 160 then d3653 (change p 247 (some 246)) else d3712 (change p 247 (some 246))) = d7335 p
  rw [sub13255, sub13314]
  rfl
theorem sub13316 (p : Pattern) : d3714 (change p 247 (some 246)) = d7336 p := by
  change (if p 141 then d3713 (change p 247 (some 246)) else d3709 (change p 247 (some 246))) = d7336 p
  rw [sub13315, sub13311]
  rfl
theorem sub13317 (p : Pattern) : d3715 (change p 247 (some 246)) = d7374 p := by
  change (if p 138 then d3695 (change p 247 (some 246)) else d3714 (change p 247 (some 246))) = d7374 p
  rw [sub13297, sub13316]
  rfl
theorem sub13318 (p : Pattern) : d3716 (change p 247 (some 246)) = d7385 p := by
  change (if p 138 then d12 (change p 247 (some 246)) else d3695 (change p 247 (some 246))) = d7385 p
  rw [sub13135, sub13297]
  rfl
theorem sub13319 (p : Pattern) : d3717 (change p 247 (some 246)) = d7386 p := by
  change (if p 116 then d3716 (change p 247 (some 246)) else d3715 (change p 247 (some 246))) = d7386 p
  rw [sub13318, sub13317]
  rfl
end NetHack.Sokoban22Refined85
