import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode504 (p : Pattern) : eval read p 4785011 = NetHack.Sokoban12CostPartition.d504 p := by
  change eval read p 4785011 = (if p 141 then NetHack.Sokoban12CostPartition.d503 p else NetHack.Sokoban12CostPartition.d501 p)
  have code : read 4785011 = .branch 141 4392010 4392011 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode501 p, oldNode503 p]
theorem oldNode505 (p : Pattern) : eval read p 4392012 = NetHack.Sokoban12CostPartition.d505 p := by
  change eval read p 4392012 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 4392012 = .branch 160 3671966 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode55 p]
theorem oldNode506 (p : Pattern) : eval read p 4392013 = NetHack.Sokoban12CostPartition.d506 p := by
  change eval read p 4392013 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d502 p)
  have code : read 4392013 = .branch 160 3999627 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode502 p, oldNode65 p]
theorem oldNode507 (p : Pattern) : eval read p 4785012 = NetHack.Sokoban12CostPartition.d507 p := by
  change eval read p 4785012 = (if p 141 then NetHack.Sokoban12CostPartition.d506 p else NetHack.Sokoban12CostPartition.d505 p)
  have code : read 4785012 = .branch 141 4392012 4392013 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode505 p, oldNode506 p]
theorem oldNode508 (p : Pattern) : eval read p 4981426 = NetHack.Sokoban12CostPartition.d508 p := by
  change eval read p 4981426 = (if p 134 then NetHack.Sokoban12CostPartition.d507 p else NetHack.Sokoban12CostPartition.d504 p)
  have code : read 4981426 = .branch 134 4785011 4785012 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode504 p, oldNode507 p]
theorem oldNode509 (p : Pattern) : eval read p 4523418 = NetHack.Sokoban12CostPartition.d509 p := by
  change eval read p 4523418 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d501 p)
  have code : read 4523418 = .branch 158 4392010 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode501 p, oldNode55 p]
theorem oldNode510 (p : Pattern) : eval read p 4523419 = NetHack.Sokoban12CostPartition.d510 p := by
  change eval read p 4523419 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d503 p)
  have code : read 4523419 = .branch 158 4392011 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode503 p, oldNode65 p]
theorem oldNode511 (p : Pattern) : eval read p 4785013 = NetHack.Sokoban12CostPartition.d511 p := by
  change eval read p 4785013 = (if p 141 then NetHack.Sokoban12CostPartition.d510 p else NetHack.Sokoban12CostPartition.d509 p)
  have code : read 4785013 = .branch 141 4523418 4523419 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode509 p, oldNode510 p]
theorem oldNode512 (p : Pattern) : eval read p 4523420 = NetHack.Sokoban12CostPartition.d512 p := by
  change eval read p 4523420 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d505 p)
  have code : read 4523420 = .branch 158 4392012 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode505 p, oldNode55 p]
theorem oldNode513 (p : Pattern) : eval read p 4523421 = NetHack.Sokoban12CostPartition.d513 p := by
  change eval read p 4523421 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d506 p)
  have code : read 4523421 = .branch 158 4392013 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode506 p, oldNode65 p]
theorem oldNode514 (p : Pattern) : eval read p 4785014 = NetHack.Sokoban12CostPartition.d514 p := by
  change eval read p 4785014 = (if p 141 then NetHack.Sokoban12CostPartition.d513 p else NetHack.Sokoban12CostPartition.d512 p)
  have code : read 4785014 = .branch 141 4523420 4523421 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode512 p, oldNode513 p]
theorem oldNode515 (p : Pattern) : eval read p 4981427 = NetHack.Sokoban12CostPartition.d515 p := by
  change eval read p 4981427 = (if p 134 then NetHack.Sokoban12CostPartition.d514 p else NetHack.Sokoban12CostPartition.d511 p)
  have code : read 4981427 = .branch 134 4785013 4785014 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode511 p, oldNode514 p]
theorem oldNode516 (p : Pattern) : eval read p 5046766 = NetHack.Sokoban12CostPartition.d516 p := by
  change eval read p 5046766 = (if p 133 then NetHack.Sokoban12CostPartition.d515 p else NetHack.Sokoban12CostPartition.d508 p)
  have code : read 5046766 = .branch 133 4981426 4981427 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode508 p, oldNode515 p]
theorem oldNode517 (p : Pattern) : eval read p 5046767 = NetHack.Sokoban12CostPartition.d517 p := by
  change eval read p 5046767 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d515 p)
  have code : read 5046767 = .branch 133 4981427 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode515 p, oldNode66 p]
theorem oldNode518 (p : Pattern) : eval read p 5112175 = NetHack.Sokoban12CostPartition.d518 p := by
  change eval read p 5112175 = (if p 132 then NetHack.Sokoban12CostPartition.d517 p else NetHack.Sokoban12CostPartition.d516 p)
  have code : read 5112175 = .branch 132 5046766 5046767 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode516 p, oldNode517 p]
theorem oldNode519 (p : Pattern) : eval read p 4981428 = NetHack.Sokoban12CostPartition.d519 p := by
  change eval read p 4981428 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d504 p)
  have code : read 4981428 = .branch 134 4785011 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode504 p, oldNode66 p]
theorem oldNode520 (p : Pattern) : eval read p 4981429 = NetHack.Sokoban12CostPartition.d520 p := by
  change eval read p 4981429 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d511 p)
  have code : read 4981429 = .branch 134 4785013 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode511 p, oldNode66 p]
theorem oldNode521 (p : Pattern) : eval read p 5046768 = NetHack.Sokoban12CostPartition.d521 p := by
  change eval read p 5046768 = (if p 133 then NetHack.Sokoban12CostPartition.d520 p else NetHack.Sokoban12CostPartition.d519 p)
  have code : read 5046768 = .branch 133 4981428 4981429 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode519 p, oldNode520 p]
theorem oldNode522 (p : Pattern) : eval read p 5046769 = NetHack.Sokoban12CostPartition.d522 p := by
  change eval read p 5046769 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d520 p)
  have code : read 5046769 = .branch 133 4981429 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode520 p, oldNode66 p]
theorem oldNode523 (p : Pattern) : eval read p 5112176 = NetHack.Sokoban12CostPartition.d523 p := by
  change eval read p 5112176 = (if p 132 then NetHack.Sokoban12CostPartition.d522 p else NetHack.Sokoban12CostPartition.d521 p)
  have code : read 5112176 = .branch 132 5046768 5046769 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode521 p, oldNode522 p]
theorem oldNode524 (p : Pattern) : eval read p 5439698 = NetHack.Sokoban12CostPartition.d524 p := by
  change eval read p 5439698 = (if p 108 then NetHack.Sokoban12CostPartition.d523 p else NetHack.Sokoban12CostPartition.d518 p)
  have code : read 5439698 = .branch 108 5112175 5112176 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode518 p, oldNode523 p]
theorem oldNode525 (p : Pattern) : eval read p 3411921 = NetHack.Sokoban12CostPartition.d525 p := by
  change eval read p 3411921 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3411921 = .branch 192 2 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode526 (p : Pattern) : eval read p 3737614 = NetHack.Sokoban12CostPartition.d526 p := by
  change eval read p 3737614 = (if p 186 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 3737614 = .branch 186 3411920 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode527 (p : Pattern) : eval read p 4392014 = NetHack.Sokoban12CostPartition.d527 p := by
  change eval read p 4392014 = (if p 160 then NetHack.Sokoban12CostPartition.d526 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 4392014 = .branch 160 3411920 3737614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode526 p]
end NetHack.Soko12Forward220.Shared
