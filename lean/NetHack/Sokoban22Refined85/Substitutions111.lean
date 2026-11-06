/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13320 (p : Pattern) : d3718 (change p 247 (some 246)) = d7387 p := by
  change (if p 115 then d3717 (change p 247 (some 246)) else d3706 (change p 247 (some 246))) = d7387 p
  rw [sub13319, sub13308]
  rfl
theorem sub13321 (p : Pattern) : d3719 (change p 247 (some 246)) = d0 p := by
  change d13 (change p 247 (some 246)) = d0 p
  exact sub13120 p
theorem sub13322 (p : Pattern) : d3720 (change p 247 (some 246)) = d0 p := by
  change (if p 225 then d13 (change p 247 (some 246)) else d3719 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13321]
  simp only [ite_self]
theorem sub13323 (p : Pattern) : d3721 (change p 247 (some 246)) = d0 p := by
  change (if p 224 then d13 (change p 247 (some 246)) else d3720 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13322]
  simp only [ite_self]
theorem sub13324 (p : Pattern) : d3722 (change p 247 (some 246)) = d7247 p := by
  change (if p 204 then d3545 (change p 247 (some 246)) else d3721 (change p 247 (some 246))) = d7247 p
  rw [sub13128, sub13323]
  rfl
theorem sub13325 (p : Pattern) : d3723 (change p 247 (some 246)) = d7251 p := by
  change (if p 182 then d3550 (change p 247 (some 246)) else d3722 (change p 247 (some 246))) = d7251 p
  rw [sub13136, sub13324]
  rfl
theorem sub13326 (p : Pattern) : d3724 (change p 247 (some 246)) = d7251 p := by
  change (if p 163 then d3553 (change p 247 (some 246)) else d3723 (change p 247 (some 246))) = d7251 p
  rw [sub13139, sub13325]
  simp only [ite_self]
theorem sub13327 (p : Pattern) : d3725 (change p 247 (some 246)) = d7260 p := by
  change (if p 162 then d3564 (change p 247 (some 246)) else d3724 (change p 247 (some 246))) = d7260 p
  rw [sub13154, sub13326]
  rfl
theorem sub13328 (p : Pattern) : d3726 (change p 247 (some 246)) = d7270 p := by
  change (if p 161 then d3575 (change p 247 (some 246)) else d3725 (change p 247 (some 246))) = d7270 p
  rw [sub13170, sub13327]
  rfl
theorem sub13329 (p : Pattern) : d3727 (change p 247 (some 246)) = d7303 p := by
  change (if p 160 then d3614 (change p 247 (some 246)) else d3726 (change p 247 (some 246))) = d7303 p
  rw [sub13215, sub13328]
  rfl
theorem sub13330 (p : Pattern) : d3728 (change p 247 (some 246)) = d7336 p := by
  change (if p 141 then d3713 (change p 247 (some 246)) else d3727 (change p 247 (some 246))) = d7336 p
  rw [sub13315, sub13329]
  rfl
theorem sub13331 (p : Pattern) : d3729 (change p 247 (some 246)) = d7374 p := by
  change (if p 138 then d3695 (change p 247 (some 246)) else d3728 (change p 247 (some 246))) = d7374 p
  rw [sub13297, sub13330]
  rfl
theorem sub13332 (p : Pattern) : d3730 (change p 247 (some 246)) = d7384 p := by
  change (if p 116 then d3705 (change p 247 (some 246)) else d3729 (change p 247 (some 246))) = d7384 p
  rw [sub13307, sub13331]
  rfl
theorem sub13333 (p : Pattern) : d3731 (change p 247 (some 246)) = d7387 p := by
  change (if p 115 then d3717 (change p 247 (some 246)) else d3730 (change p 247 (some 246))) = d7387 p
  rw [sub13319, sub13332]
  rfl
theorem sub13334 (p : Pattern) : d3732 (change p 247 (some 246)) = d7387 p := by
  change (if p 71 then d3731 (change p 247 (some 246)) else d3718 (change p 247 (some 246))) = d7387 p
  rw [sub13333, sub13320]
  simp only [ite_self]
theorem sub13335 (p : Pattern) : d1 (change p 247 (some 246)) = d1 p := by
  rfl
theorem sub13336 (p : Pattern) : d102 (change p 247 (some 246)) = d1 p := by
  change d1 (change p 247 (some 246)) = d1 p
  exact sub13335 p
theorem sub13337 (p : Pattern) : d3733 (change p 247 (some 246)) = d1 p := by
  change d102 (change p 247 (some 246)) = d1 p
  exact sub13336 p
theorem sub13338 (p : Pattern) : d3734 (change p 247 (some 246)) = d1 p := by
  change (if p 225 then d102 (change p 247 (some 246)) else d3733 (change p 247 (some 246))) = d1 p
  rw [sub13336, sub13337]
  simp only [ite_self]
theorem sub13339 (p : Pattern) : d3735 (change p 247 (some 246)) = d1 p := by
  change (if p 224 then d102 (change p 247 (some 246)) else d3734 (change p 247 (some 246))) = d1 p
  rw [sub13336, sub13338]
  simp only [ite_self]
theorem sub13340 (p : Pattern) : d5 (change p 247 (some 246)) = d5 p := by
  rfl
theorem sub13341 (p : Pattern) : d106 (change p 247 (some 246)) = d5 p := by
  change d5 (change p 247 (some 246)) = d5 p
  exact sub13340 p
theorem sub13342 (p : Pattern) : d3736 (change p 247 (some 246)) = d5 p := by
  change d106 (change p 247 (some 246)) = d5 p
  exact sub13341 p
theorem sub13343 (p : Pattern) : d3737 (change p 247 (some 246)) = d7388 p := by
  change (if p 225 then d3736 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7388 p
  rw [sub13342, sub13336]
  rfl
theorem sub13344 (p : Pattern) : d3738 (change p 247 (some 246)) = d7389 p := by
  change (if p 224 then d3736 (change p 247 (some 246)) else d3737 (change p 247 (some 246))) = d7389 p
  rw [sub13342, sub13343]
  rfl
theorem sub13345 (p : Pattern) : d3739 (change p 247 (some 246)) = d7390 p := by
  change (if p 204 then d3738 (change p 247 (some 246)) else d3735 (change p 247 (some 246))) = d7390 p
  rw [sub13344, sub13339]
  rfl
theorem sub13346 (p : Pattern) : d3 (change p 247 (some 246)) = d3 p := by
  rfl
theorem sub13347 (p : Pattern) : d115 (change p 247 (some 246)) = d3 p := by
  change d3 (change p 247 (some 246)) = d3 p
  exact sub13346 p
theorem sub13348 (p : Pattern) : d3740 (change p 247 (some 246)) = d3 p := by
  change d115 (change p 247 (some 246)) = d3 p
  exact sub13347 p
theorem sub13349 (p : Pattern) : d3741 (change p 247 (some 246)) = d7391 p := by
  change (if p 225 then d3740 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7391 p
  rw [sub13348, sub13336]
  rfl
theorem sub13350 (p : Pattern) : d3742 (change p 247 (some 246)) = d7392 p := by
  change (if p 224 then d3740 (change p 247 (some 246)) else d3741 (change p 247 (some 246))) = d7392 p
  rw [sub13348, sub13349]
  rfl
theorem sub13351 (p : Pattern) : d3743 (change p 247 (some 246)) = d7393 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3742 (change p 247 (some 246))) = d7393 p
  rw [sub13135, sub13350]
  rfl
theorem sub13352 (p : Pattern) : d3744 (change p 247 (some 246)) = d7394 p := by
  change (if p 182 then d3743 (change p 247 (some 246)) else d3739 (change p 247 (some 246))) = d7394 p
  rw [sub13351, sub13345]
  rfl
theorem sub13353 (p : Pattern) : d3745 (change p 247 (some 246)) = d7390 p := by
  change (if p 204 then d3738 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7390 p
  rw [sub13344, sub13336]
  rfl
theorem sub13354 (p : Pattern) : d3746 (change p 247 (some 246)) = d7394 p := by
  change (if p 182 then d3743 (change p 247 (some 246)) else d3745 (change p 247 (some 246))) = d7394 p
  rw [sub13351, sub13353]
  rfl
theorem sub13355 (p : Pattern) : d3747 (change p 247 (some 246)) = d7394 p := by
  change (if p 163 then d3746 (change p 247 (some 246)) else d3744 (change p 247 (some 246))) = d7394 p
  rw [sub13354, sub13352]
  simp only [ite_self]
theorem sub13356 (p : Pattern) : d3748 (change p 247 (some 246)) = d9 p := by
  change d23 (change p 247 (some 246)) = d9 p
  exact sub13157 p
theorem sub13357 (p : Pattern) : d3749 (change p 247 (some 246)) = d7395 p := by
  change (if p 225 then d3748 (change p 247 (some 246)) else d106 (change p 247 (some 246))) = d7395 p
  rw [sub13356, sub13341]
  rfl
theorem sub13358 (p : Pattern) : d3750 (change p 247 (some 246)) = d7396 p := by
  change (if p 224 then d3748 (change p 247 (some 246)) else d3749 (change p 247 (some 246))) = d7396 p
  rw [sub13356, sub13357]
  rfl
theorem sub13359 (p : Pattern) : d3751 (change p 247 (some 246)) = d7397 p := by
  change (if p 204 then d3750 (change p 247 (some 246)) else d106 (change p 247 (some 246))) = d7397 p
  rw [sub13358, sub13341]
  rfl
theorem sub13360 (p : Pattern) : d7 (change p 247 (some 246)) = d7 p := by
  rfl
theorem sub13361 (p : Pattern) : d119 (change p 247 (some 246)) = d7 p := by
  change d7 (change p 247 (some 246)) = d7 p
  exact sub13360 p
theorem sub13362 (p : Pattern) : d3752 (change p 247 (some 246)) = d7 p := by
  change d119 (change p 247 (some 246)) = d7 p
  exact sub13361 p
theorem sub13363 (p : Pattern) : d3753 (change p 247 (some 246)) = d7398 p := by
  change (if p 225 then d3752 (change p 247 (some 246)) else d106 (change p 247 (some 246))) = d7398 p
  rw [sub13362, sub13341]
  rfl
theorem sub13364 (p : Pattern) : d3754 (change p 247 (some 246)) = d7399 p := by
  change (if p 224 then d3752 (change p 247 (some 246)) else d3753 (change p 247 (some 246))) = d7399 p
  rw [sub13362, sub13363]
  rfl
theorem sub13365 (p : Pattern) : d3755 (change p 247 (some 246)) = d7400 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3754 (change p 247 (some 246))) = d7400 p
  rw [sub13135, sub13364]
  rfl
theorem sub13366 (p : Pattern) : d3756 (change p 247 (some 246)) = d7401 p := by
  change (if p 182 then d3755 (change p 247 (some 246)) else d3751 (change p 247 (some 246))) = d7401 p
  rw [sub13365, sub13359]
  rfl
theorem sub13367 (p : Pattern) : d3757 (change p 247 (some 246)) = d7402 p := by
  change (if p 163 then d3756 (change p 247 (some 246)) else d3746 (change p 247 (some 246))) = d7402 p
  rw [sub13366, sub13354]
  rfl
theorem sub13368 (p : Pattern) : d3758 (change p 247 (some 246)) = d7403 p := by
  change (if p 162 then d3757 (change p 247 (some 246)) else d3747 (change p 247 (some 246))) = d7403 p
  rw [sub13367, sub13355]
  rfl
theorem sub13369 (p : Pattern) : d3759 (change p 247 (some 246)) = d7404 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3636 (change p 247 (some 246))) = d7404 p
  rw [sub13135, sub13238]
  rfl
theorem sub13370 (p : Pattern) : d3760 (change p 247 (some 246)) = d7405 p := by
  change (if p 162 then d3759 (change p 247 (some 246)) else d3757 (change p 247 (some 246))) = d7405 p
  rw [sub13369, sub13367]
  rfl
theorem sub13371 (p : Pattern) : d3761 (change p 247 (some 246)) = d7406 p := by
  change (if p 161 then d3760 (change p 247 (some 246)) else d3758 (change p 247 (some 246))) = d7406 p
  rw [sub13370, sub13368]
  rfl
theorem sub13372 (p : Pattern) : d3762 (change p 247 (some 246)) = d7 p := by
  change d119 (change p 247 (some 246)) = d7 p
  exact sub13361 p
theorem sub13373 (p : Pattern) : d3763 (change p 247 (some 246)) = d7407 p := by
  change (if p 225 then d3762 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7407 p
  rw [sub13372, sub13336]
  rfl
theorem sub13374 (p : Pattern) : d1955 (change p 247 (some 246)) = d10 p := by
  change d57 (change p 247 (some 246)) = d10 p
  exact sub13189 p
theorem sub13375 (p : Pattern) : d3764 (change p 247 (some 246)) = d7408 p := by
  change (if p 225 then d1955 (change p 247 (some 246)) else d3736 (change p 247 (some 246))) = d7408 p
  rw [sub13374, sub13342]
  rfl
theorem sub13376 (p : Pattern) : d3765 (change p 247 (some 246)) = d7409 p := by
  change (if p 224 then d3764 (change p 247 (some 246)) else d3763 (change p 247 (some 246))) = d7409 p
  rw [sub13375, sub13373]
  rfl
theorem sub13377 (p : Pattern) : d3766 (change p 247 (some 246)) = d7410 p := by
  change (if p 204 then d3765 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7410 p
  rw [sub13376, sub13336]
  rfl
theorem sub13378 (p : Pattern) : d3767 (change p 247 (some 246)) = d9 p := by
  change d23 (change p 247 (some 246)) = d9 p
  exact sub13157 p
theorem sub13379 (p : Pattern) : d3768 (change p 247 (some 246)) = d7411 p := by
  change (if p 225 then d3767 (change p 247 (some 246)) else d115 (change p 247 (some 246))) = d7411 p
  rw [sub13378, sub13347]
  rfl
theorem sub13380 (p : Pattern) : d3769 (change p 247 (some 246)) = d7 p := by
  change d119 (change p 247 (some 246)) = d7 p
  exact sub13361 p
theorem sub13381 (p : Pattern) : d1896 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13382 (p : Pattern) : d3770 (change p 247 (some 246)) = d7412 p := by
  change (if p 225 then d1896 (change p 247 (some 246)) else d3769 (change p 247 (some 246))) = d7412 p
  rw [sub13381, sub13380]
  rfl
theorem sub13383 (p : Pattern) : d3771 (change p 247 (some 246)) = d7413 p := by
  change (if p 224 then d3770 (change p 247 (some 246)) else d3768 (change p 247 (some 246))) = d7413 p
  rw [sub13382, sub13379]
  rfl
theorem sub13384 (p : Pattern) : d3772 (change p 247 (some 246)) = d7414 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3771 (change p 247 (some 246))) = d7414 p
  rw [sub13135, sub13383]
  rfl
theorem sub13385 (p : Pattern) : d3773 (change p 247 (some 246)) = d7415 p := by
  change (if p 182 then d3772 (change p 247 (some 246)) else d3766 (change p 247 (some 246))) = d7415 p
  rw [sub13384, sub13377]
  rfl
theorem sub13386 (p : Pattern) : d317 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13387 (p : Pattern) : d3774 (change p 247 (some 246)) = d7412 p := by
  change (if p 225 then d317 (change p 247 (some 246)) else d119 (change p 247 (some 246))) = d7412 p
  rw [sub13386, sub13361]
  rfl
theorem sub13388 (p : Pattern) : d3775 (change p 247 (some 246)) = d11 p := by
  change d39 (change p 247 (some 246)) = d11 p
  exact sub13163 p
theorem sub13389 (p : Pattern) : d3776 (change p 247 (some 246)) = d7286 p := by
  change (if p 225 then d317 (change p 247 (some 246)) else d3775 (change p 247 (some 246))) = d7286 p
  rw [sub13386, sub13388]
  rfl
theorem sub13390 (p : Pattern) : d3777 (change p 247 (some 246)) = d7416 p := by
  change (if p 224 then d3776 (change p 247 (some 246)) else d3774 (change p 247 (some 246))) = d7416 p
  rw [sub13389, sub13387]
  rfl
theorem sub13391 (p : Pattern) : d3778 (change p 247 (some 246)) = d7417 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3777 (change p 247 (some 246))) = d7417 p
  rw [sub13135, sub13390]
  rfl
theorem sub13392 (p : Pattern) : d3779 (change p 247 (some 246)) = d7418 p := by
  change (if p 182 then d3778 (change p 247 (some 246)) else d3766 (change p 247 (some 246))) = d7418 p
  rw [sub13391, sub13377]
  rfl
theorem sub13393 (p : Pattern) : d3780 (change p 247 (some 246)) = d7419 p := by
  change (if p 163 then d3779 (change p 247 (some 246)) else d3773 (change p 247 (some 246))) = d7419 p
  rw [sub13392, sub13385]
  rfl
theorem sub13394 (p : Pattern) : d3781 (change p 247 (some 246)) = d7420 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3766 (change p 247 (some 246))) = d7420 p
  rw [sub13135, sub13377]
  rfl
theorem sub13395 (p : Pattern) : d3782 (change p 247 (some 246)) = d11 p := by
  change d39 (change p 247 (some 246)) = d11 p
  exact sub13163 p
theorem sub13396 (p : Pattern) : d3783 (change p 247 (some 246)) = d7421 p := by
  change (if p 225 then d3782 (change p 247 (some 246)) else d106 (change p 247 (some 246))) = d7421 p
  rw [sub13395, sub13341]
  rfl
theorem sub13397 (p : Pattern) : d348 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13398 (p : Pattern) : d3784 (change p 247 (some 246)) = d7261 p := by
  change (if p 225 then d348 (change p 247 (some 246)) else d3748 (change p 247 (some 246))) = d7261 p
  rw [sub13397, sub13356]
  rfl
theorem sub13399 (p : Pattern) : d3785 (change p 247 (some 246)) = d7422 p := by
  change (if p 224 then d3784 (change p 247 (some 246)) else d3783 (change p 247 (some 246))) = d7422 p
  rw [sub13398, sub13396]
  rfl
theorem sub13400 (p : Pattern) : d3786 (change p 247 (some 246)) = d7423 p := by
  change (if p 204 then d3785 (change p 247 (some 246)) else d106 (change p 247 (some 246))) = d7423 p
  rw [sub13399, sub13341]
  rfl
theorem sub13401 (p : Pattern) : d3787 (change p 247 (some 246)) = d7424 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3786 (change p 247 (some 246))) = d7424 p
  rw [sub13135, sub13400]
  rfl
theorem sub13402 (p : Pattern) : d3788 (change p 247 (some 246)) = d7425 p := by
  change (if p 163 then d3787 (change p 247 (some 246)) else d3781 (change p 247 (some 246))) = d7425 p
  rw [sub13401, sub13394]
  rfl
theorem sub13403 (p : Pattern) : d3789 (change p 247 (some 246)) = d7426 p := by
  change (if p 162 then d3788 (change p 247 (some 246)) else d3780 (change p 247 (some 246))) = d7426 p
  rw [sub13402, sub13393]
  rfl
theorem sub13404 (p : Pattern) : d3790 (change p 247 (some 246)) = d7427 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3648 (change p 247 (some 246))) = d7427 p
  rw [sub13135, sub13250]
  rfl
theorem sub13405 (p : Pattern) : d3791 (change p 247 (some 246)) = d7428 p := by
  change (if p 162 then d3790 (change p 247 (some 246)) else d3788 (change p 247 (some 246))) = d7428 p
  rw [sub13404, sub13402]
  rfl
theorem sub13406 (p : Pattern) : d3792 (change p 247 (some 246)) = d7429 p := by
  change (if p 161 then d3791 (change p 247 (some 246)) else d3789 (change p 247 (some 246))) = d7429 p
  rw [sub13405, sub13403]
  rfl
theorem sub13407 (p : Pattern) : d3793 (change p 247 (some 246)) = d7430 p := by
  change (if p 160 then d3792 (change p 247 (some 246)) else d3761 (change p 247 (some 246))) = d7430 p
  rw [sub13406, sub13371]
  rfl
theorem sub13408 (p : Pattern) : d3794 (change p 247 (some 246)) = d7431 p := by
  change (if p 225 then d3769 (change p 247 (some 246)) else d115 (change p 247 (some 246))) = d7431 p
  rw [sub13380, sub13347]
  rfl
theorem sub13409 (p : Pattern) : d3795 (change p 247 (some 246)) = d7432 p := by
  change (if p 224 then d3769 (change p 247 (some 246)) else d3794 (change p 247 (some 246))) = d7432 p
  rw [sub13380, sub13408]
  rfl
theorem sub13410 (p : Pattern) : d3796 (change p 247 (some 246)) = d7433 p := by
  change (if p 204 then d3795 (change p 247 (some 246)) else d115 (change p 247 (some 246))) = d7433 p
  rw [sub13409, sub13347]
  rfl
theorem sub13411 (p : Pattern) : d3797 (change p 247 (some 246)) = d5 p := by
  change d106 (change p 247 (some 246)) = d5 p
  exact sub13341 p
theorem sub13412 (p : Pattern) : d3798 (change p 247 (some 246)) = d7434 p := by
  change (if p 225 then d3797 (change p 247 (some 246)) else d115 (change p 247 (some 246))) = d7434 p
  rw [sub13411, sub13347]
  rfl
theorem sub13413 (p : Pattern) : d3799 (change p 247 (some 246)) = d7435 p := by
  change (if p 224 then d3797 (change p 247 (some 246)) else d3798 (change p 247 (some 246))) = d7435 p
  rw [sub13411, sub13412]
  rfl
theorem sub13414 (p : Pattern) : d3800 (change p 247 (some 246)) = d7436 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3799 (change p 247 (some 246))) = d7436 p
  rw [sub13135, sub13413]
  rfl
theorem sub13415 (p : Pattern) : d3801 (change p 247 (some 246)) = d7437 p := by
  change (if p 182 then d3800 (change p 247 (some 246)) else d3796 (change p 247 (some 246))) = d7437 p
  rw [sub13414, sub13410]
  rfl
theorem sub13416 (p : Pattern) : d3802 (change p 247 (some 246)) = d7438 p := by
  change (if p 163 then d3801 (change p 247 (some 246)) else d3746 (change p 247 (some 246))) = d7438 p
  rw [sub13415, sub13354]
  rfl
theorem sub13417 (p : Pattern) : d3803 (change p 247 (some 246)) = d7439 p := by
  change (if p 163 then d3636 (change p 247 (some 246)) else d3756 (change p 247 (some 246))) = d7439 p
  rw [sub13238, sub13366]
  rfl
theorem sub13418 (p : Pattern) : d3804 (change p 247 (some 246)) = d7440 p := by
  change (if p 162 then d3803 (change p 247 (some 246)) else d3802 (change p 247 (some 246))) = d7440 p
  rw [sub13417, sub13416]
  rfl
theorem sub13419 (p : Pattern) : d3805 (change p 247 (some 246)) = d7441 p := by
  change (if p 163 then d3639 (change p 247 (some 246)) else d3756 (change p 247 (some 246))) = d7441 p
  rw [sub13241, sub13366]
  rfl
theorem sub13420 (p : Pattern) : d3806 (change p 247 (some 246)) = d7442 p := by
  change (if p 162 then d12 (change p 247 (some 246)) else d3805 (change p 247 (some 246))) = d7442 p
  rw [sub13135, sub13419]
  rfl
theorem sub13421 (p : Pattern) : d3807 (change p 247 (some 246)) = d7443 p := by
  change (if p 161 then d3806 (change p 247 (some 246)) else d3804 (change p 247 (some 246))) = d7443 p
  rw [sub13420, sub13418]
  rfl
theorem sub13422 (p : Pattern) : d3808 (change p 247 (some 246)) = d7444 p := by
  change (if p 204 then d3771 (change p 247 (some 246)) else d115 (change p 247 (some 246))) = d7444 p
  rw [sub13383, sub13347]
  rfl
theorem sub13423 (p : Pattern) : d3809 (change p 247 (some 246)) = d7445 p := by
  change (if p 182 then d12 (change p 247 (some 246)) else d3808 (change p 247 (some 246))) = d7445 p
  rw [sub13135, sub13422]
  rfl
theorem sub13424 (p : Pattern) : d3810 (change p 247 (some 246)) = d7446 p := by
  change (if p 163 then d3809 (change p 247 (some 246)) else d3779 (change p 247 (some 246))) = d7446 p
  rw [sub13423, sub13392]
  rfl
theorem sub13425 (p : Pattern) : d3811 (change p 247 (some 246)) = d7447 p := by
  change (if p 163 then d3648 (change p 247 (some 246)) else d3787 (change p 247 (some 246))) = d7447 p
  rw [sub13250, sub13401]
  rfl
theorem sub13426 (p : Pattern) : d3812 (change p 247 (some 246)) = d7448 p := by
  change (if p 162 then d3811 (change p 247 (some 246)) else d3810 (change p 247 (some 246))) = d7448 p
  rw [sub13425, sub13424]
  rfl
theorem sub13427 (p : Pattern) : d3813 (change p 247 (some 246)) = d7449 p := by
  change (if p 163 then d3650 (change p 247 (some 246)) else d3787 (change p 247 (some 246))) = d7449 p
  rw [sub13252, sub13401]
  rfl
theorem sub13428 (p : Pattern) : d3814 (change p 247 (some 246)) = d7450 p := by
  change (if p 162 then d12 (change p 247 (some 246)) else d3813 (change p 247 (some 246))) = d7450 p
  rw [sub13135, sub13427]
  rfl
theorem sub13429 (p : Pattern) : d3815 (change p 247 (some 246)) = d7451 p := by
  change (if p 161 then d3814 (change p 247 (some 246)) else d3812 (change p 247 (some 246))) = d7451 p
  rw [sub13428, sub13426]
  rfl
theorem sub13430 (p : Pattern) : d3816 (change p 247 (some 246)) = d7452 p := by
  change (if p 160 then d3815 (change p 247 (some 246)) else d3807 (change p 247 (some 246))) = d7452 p
  rw [sub13429, sub13421]
  rfl
theorem sub13431 (p : Pattern) : d3817 (change p 247 (some 246)) = d7453 p := by
  change (if p 141 then d3816 (change p 247 (some 246)) else d3793 (change p 247 (some 246))) = d7453 p
  rw [sub13430, sub13407]
  rfl
theorem sub13432 (p : Pattern) : d3818 (change p 247 (some 246)) = d7398 p := by
  change (if p 225 then d3762 (change p 247 (some 246)) else d3736 (change p 247 (some 246))) = d7398 p
  rw [sub13372, sub13342]
  rfl
theorem sub13433 (p : Pattern) : d3819 (change p 247 (some 246)) = d7454 p := by
  change (if p 224 then d3818 (change p 247 (some 246)) else d3763 (change p 247 (some 246))) = d7454 p
  rw [sub13432, sub13373]
  rfl
theorem sub13434 (p : Pattern) : d3820 (change p 247 (some 246)) = d7455 p := by
  change (if p 204 then d3819 (change p 247 (some 246)) else d102 (change p 247 (some 246))) = d7455 p
  rw [sub13433, sub13336]
  rfl
theorem sub13435 (p : Pattern) : d3821 (change p 247 (some 246)) = d7456 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3738 (change p 247 (some 246))) = d7456 p
  rw [sub13135, sub13344]
  rfl
theorem sub13436 (p : Pattern) : d3822 (change p 247 (some 246)) = d7457 p := by
  change (if p 182 then d3821 (change p 247 (some 246)) else d3820 (change p 247 (some 246))) = d7457 p
  rw [sub13435, sub13434]
  rfl
theorem sub13437 (p : Pattern) : d3823 (change p 247 (some 246)) = d9 p := by
  change d23 (change p 247 (some 246)) = d9 p
  exact sub13157 p
theorem sub13438 (p : Pattern) : d3824 (change p 247 (some 246)) = d7395 p := by
  change (if p 225 then d3823 (change p 247 (some 246)) else d3736 (change p 247 (some 246))) = d7395 p
  rw [sub13437, sub13342]
  rfl
theorem sub13439 (p : Pattern) : d3825 (change p 247 (some 246)) = d7458 p := by
  change (if p 224 then d3824 (change p 247 (some 246)) else d3763 (change p 247 (some 246))) = d7458 p
  rw [sub13438, sub13373]
  rfl
end NetHack.Sokoban22Refined85
