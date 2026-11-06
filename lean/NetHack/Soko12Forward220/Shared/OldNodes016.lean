import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode528 (p : Pattern) : eval read p 3411923 = NetHack.Sokoban12CostPartition.d528 p := by
  change eval read p 3411923 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 3411923 = .branch 192 1638542 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode5 p]
theorem oldNode529 (p : Pattern) : eval read p 3737615 = NetHack.Sokoban12CostPartition.d529 p := by
  change eval read p 3737615 = (if p 186 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 3737615 = .branch 186 3411922 3411923 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode528 p]
theorem oldNode530 (p : Pattern) : eval read p 3999629 = NetHack.Sokoban12CostPartition.d530 p := by
  change eval read p 3999629 = (if p 168 then NetHack.Sokoban12CostPartition.d529 p else NetHack.Sokoban12CostPartition.d526 p)
  have code : read 3999629 = .branch 168 3737614 3737615 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode526 p, oldNode529 p]
theorem oldNode531 (p : Pattern) : eval read p 4392015 = NetHack.Sokoban12CostPartition.d531 p := by
  change eval read p 4392015 = (if p 160 then NetHack.Sokoban12CostPartition.d530 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 4392015 = .branch 160 3999628 3999629 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode530 p]
theorem oldNode532 (p : Pattern) : eval read p 4785015 = NetHack.Sokoban12CostPartition.d532 p := by
  change eval read p 4785015 = (if p 141 then NetHack.Sokoban12CostPartition.d531 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 4785015 = .branch 141 4392014 4392015 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode531 p]
theorem oldNode533 (p : Pattern) : eval read p 4392016 = NetHack.Sokoban12CostPartition.d533 p := by
  change eval read p 4392016 = (if p 160 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 4392016 = .branch 160 3411920 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode534 (p : Pattern) : eval read p 3671970 = NetHack.Sokoban12CostPartition.d534 p := by
  change eval read p 3671970 = (if p 187 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 3671970 = .branch 187 3411920 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode535 (p : Pattern) : eval read p 3737616 = NetHack.Sokoban12CostPartition.d535 p := by
  change eval read p 3737616 = (if p 186 then NetHack.Sokoban12CostPartition.d534 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 3737616 = .branch 186 3411920 3671970 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode534 p]
theorem oldNode536 (p : Pattern) : eval read p 4392017 = NetHack.Sokoban12CostPartition.d536 p := by
  change eval read p 4392017 = (if p 160 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 4392017 = .branch 160 3737616 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode525 p]
theorem oldNode537 (p : Pattern) : eval read p 4457778 = NetHack.Sokoban12CostPartition.d537 p := by
  change eval read p 4457778 = (if p 159 then NetHack.Sokoban12CostPartition.d536 p else NetHack.Sokoban12CostPartition.d533 p)
  have code : read 4457778 = .branch 159 4392016 4392017 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode533 p, oldNode536 p]
theorem oldNode538 (p : Pattern) : eval read p 4523422 = NetHack.Sokoban12CostPartition.d538 p := by
  change eval read p 4523422 = (if p 158 then NetHack.Sokoban12CostPartition.d537 p else NetHack.Sokoban12CostPartition.d533 p)
  have code : read 4523422 = .branch 158 4392016 4457778 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode533 p, oldNode537 p]
theorem oldNode539 (p : Pattern) : eval read p 3999630 = NetHack.Sokoban12CostPartition.d539 p := by
  change eval read p 3999630 = (if p 168 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d525 p)
  have code : read 3999630 = .branch 168 3411921 3411923 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode525 p, oldNode528 p]
theorem oldNode540 (p : Pattern) : eval read p 4392018 = NetHack.Sokoban12CostPartition.d540 p := by
  change eval read p 4392018 = (if p 160 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 4392018 = .branch 160 3999628 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode539 p]
theorem oldNode541 (p : Pattern) : eval read p 3671971 = NetHack.Sokoban12CostPartition.d541 p := by
  change eval read p 3671971 = (if p 187 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 3671971 = .branch 187 3411922 3411923 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode528 p]
theorem oldNode542 (p : Pattern) : eval read p 3737617 = NetHack.Sokoban12CostPartition.d542 p := by
  change eval read p 3737617 = (if p 186 then NetHack.Sokoban12CostPartition.d541 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 3737617 = .branch 186 3411922 3671971 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode541 p]
theorem oldNode543 (p : Pattern) : eval read p 3999631 = NetHack.Sokoban12CostPartition.d543 p := by
  change eval read p 3999631 = (if p 168 then NetHack.Sokoban12CostPartition.d542 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 3999631 = .branch 168 3737616 3737617 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode542 p]
theorem oldNode544 (p : Pattern) : eval read p 4392019 = NetHack.Sokoban12CostPartition.d544 p := by
  change eval read p 4392019 = (if p 160 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d543 p)
  have code : read 4392019 = .branch 160 3999631 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode543 p, oldNode539 p]
theorem oldNode545 (p : Pattern) : eval read p 4457779 = NetHack.Sokoban12CostPartition.d545 p := by
  change eval read p 4457779 = (if p 159 then NetHack.Sokoban12CostPartition.d544 p else NetHack.Sokoban12CostPartition.d540 p)
  have code : read 4457779 = .branch 159 4392018 4392019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode540 p, oldNode544 p]
theorem oldNode546 (p : Pattern) : eval read p 4523423 = NetHack.Sokoban12CostPartition.d546 p := by
  change eval read p 4523423 = (if p 158 then NetHack.Sokoban12CostPartition.d545 p else NetHack.Sokoban12CostPartition.d540 p)
  have code : read 4523423 = .branch 158 4392018 4457779 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode540 p, oldNode545 p]
theorem oldNode547 (p : Pattern) : eval read p 4785016 = NetHack.Sokoban12CostPartition.d547 p := by
  change eval read p 4785016 = (if p 141 then NetHack.Sokoban12CostPartition.d546 p else NetHack.Sokoban12CostPartition.d538 p)
  have code : read 4785016 = .branch 141 4523422 4523423 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode538 p, oldNode546 p]
theorem oldNode548 (p : Pattern) : eval read p 4981430 = NetHack.Sokoban12CostPartition.d548 p := by
  change eval read p 4981430 = (if p 134 then NetHack.Sokoban12CostPartition.d547 p else NetHack.Sokoban12CostPartition.d532 p)
  have code : read 4981430 = .branch 134 4785015 4785016 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode532 p, oldNode547 p]
theorem oldNode549 (p : Pattern) : eval read p 4523424 = NetHack.Sokoban12CostPartition.d549 p := by
  change eval read p 4523424 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 4523424 = .branch 158 4392014 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode525 p]
theorem oldNode550 (p : Pattern) : eval read p 4523425 = NetHack.Sokoban12CostPartition.d550 p := by
  change eval read p 4523425 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 4523425 = .branch 158 4392015 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode539 p]
theorem oldNode551 (p : Pattern) : eval read p 4785017 = NetHack.Sokoban12CostPartition.d551 p := by
  change eval read p 4785017 = (if p 141 then NetHack.Sokoban12CostPartition.d550 p else NetHack.Sokoban12CostPartition.d549 p)
  have code : read 4785017 = .branch 141 4523424 4523425 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode549 p, oldNode550 p]
end NetHack.Soko12Forward220.Shared
