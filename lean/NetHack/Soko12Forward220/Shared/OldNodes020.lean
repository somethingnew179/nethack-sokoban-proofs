import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode624 (p : Pattern) : eval read p 4785026 = NetHack.Sokoban12CostPartition.d624 p := by
  change eval read p 4785026 = (if p 141 then NetHack.Sokoban12CostPartition.d623 p else NetHack.Sokoban12CostPartition.d622 p)
  have code : read 4785026 = .branch 141 4523438 4523439 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode622 p, oldNode623 p]
theorem oldNode625 (p : Pattern) : eval read p 4981436 = NetHack.Sokoban12CostPartition.d625 p := by
  change eval read p 4981436 = (if p 134 then NetHack.Sokoban12CostPartition.d624 p else NetHack.Sokoban12CostPartition.d621 p)
  have code : read 4981436 = .branch 134 4785025 4785026 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode621 p, oldNode624 p]
theorem oldNode626 (p : Pattern) : eval read p 5046774 = NetHack.Sokoban12CostPartition.d626 p := by
  change eval read p 5046774 = (if p 133 then NetHack.Sokoban12CostPartition.d625 p else NetHack.Sokoban12CostPartition.d618 p)
  have code : read 5046774 = .branch 133 4981435 4981436 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode618 p, oldNode625 p]
theorem oldNode627 (p : Pattern) : eval read p 4785027 = NetHack.Sokoban12CostPartition.d627 p := by
  change eval read p 4785027 = (if p 141 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d599 p)
  have code : read 4785027 = .branch 141 3999637 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode599 p, oldNode609 p]
theorem oldNode628 (p : Pattern) : eval read p 5046775 = NetHack.Sokoban12CostPartition.d628 p := by
  change eval read p 5046775 = (if p 133 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d625 p)
  have code : read 5046775 = .branch 133 4981436 4785027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode625 p, oldNode627 p]
theorem oldNode629 (p : Pattern) : eval read p 5112179 = NetHack.Sokoban12CostPartition.d629 p := by
  change eval read p 5112179 = (if p 132 then NetHack.Sokoban12CostPartition.d628 p else NetHack.Sokoban12CostPartition.d626 p)
  have code : read 5112179 = .branch 132 5046774 5046775 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode626 p, oldNode628 p]
theorem oldNode630 (p : Pattern) : eval read p 3737626 = NetHack.Sokoban12CostPartition.d630 p := by
  change eval read p 3737626 = (if p 186 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d601 p)
  have code : read 3737626 = .branch 186 3671972 3411926 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode601 p, oldNode588 p]
theorem oldNode631 (p : Pattern) : eval read p 3737627 = NetHack.Sokoban12CostPartition.d631 p := by
  change eval read p 3737627 = (if p 186 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d603 p)
  have code : read 3737627 = .branch 186 3671973 3411927 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode603 p, oldNode590 p]
theorem oldNode632 (p : Pattern) : eval read p 3999641 = NetHack.Sokoban12CostPartition.d632 p := by
  change eval read p 3999641 = (if p 168 then NetHack.Sokoban12CostPartition.d631 p else NetHack.Sokoban12CostPartition.d630 p)
  have code : read 3999641 = .branch 168 3737626 3737627 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode630 p, oldNode631 p]
theorem oldNode633 (p : Pattern) : eval read p 4392030 = NetHack.Sokoban12CostPartition.d633 p := by
  change eval read p 4392030 = (if p 160 then NetHack.Sokoban12CostPartition.d632 p else NetHack.Sokoban12CostPartition.d605 p)
  have code : read 4392030 = .branch 160 3999638 3999641 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode605 p, oldNode632 p]
theorem oldNode634 (p : Pattern) : eval read p 4457786 = NetHack.Sokoban12CostPartition.d634 p := by
  change eval read p 4457786 = (if p 159 then NetHack.Sokoban12CostPartition.d633 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 4457786 = .branch 159 4392024 4392030 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode633 p]
theorem oldNode635 (p : Pattern) : eval read p 4523440 = NetHack.Sokoban12CostPartition.d635 p := by
  change eval read p 4523440 = (if p 158 then NetHack.Sokoban12CostPartition.d634 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 4523440 = .branch 158 4392024 4457786 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode634 p]
theorem oldNode636 (p : Pattern) : eval read p 3737628 = NetHack.Sokoban12CostPartition.d636 p := by
  change eval read p 3737628 = (if p 186 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d611 p)
  have code : read 3737628 = .branch 186 3671974 3347243 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode611 p, oldNode594 p]
theorem oldNode637 (p : Pattern) : eval read p 3999642 = NetHack.Sokoban12CostPartition.d637 p := by
  change eval read p 3999642 = (if p 168 then NetHack.Sokoban12CostPartition.d636 p else NetHack.Sokoban12CostPartition.d631 p)
  have code : read 3999642 = .branch 168 3737627 3737628 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode631 p, oldNode636 p]
theorem oldNode638 (p : Pattern) : eval read p 4392031 = NetHack.Sokoban12CostPartition.d638 p := by
  change eval read p 4392031 = (if p 160 then NetHack.Sokoban12CostPartition.d637 p else NetHack.Sokoban12CostPartition.d613 p)
  have code : read 4392031 = .branch 160 3999640 3999642 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode613 p, oldNode637 p]
theorem oldNode639 (p : Pattern) : eval read p 4457787 = NetHack.Sokoban12CostPartition.d639 p := by
  change eval read p 4457787 = (if p 159 then NetHack.Sokoban12CostPartition.d638 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 4457787 = .branch 159 4392025 4392031 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode638 p]
theorem oldNode640 (p : Pattern) : eval read p 4523441 = NetHack.Sokoban12CostPartition.d640 p := by
  change eval read p 4523441 = (if p 158 then NetHack.Sokoban12CostPartition.d639 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 4523441 = .branch 158 4392025 4457787 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode639 p]
theorem oldNode641 (p : Pattern) : eval read p 4785028 = NetHack.Sokoban12CostPartition.d641 p := by
  change eval read p 4785028 = (if p 141 then NetHack.Sokoban12CostPartition.d640 p else NetHack.Sokoban12CostPartition.d635 p)
  have code : read 4785028 = .branch 141 4523440 4523441 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode635 p, oldNode640 p]
theorem oldNode642 (p : Pattern) : eval read p 4981437 = NetHack.Sokoban12CostPartition.d642 p := by
  change eval read p 4981437 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d641 p)
  have code : read 4981437 = .branch 134 4785028 4785027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode641 p, oldNode627 p]
theorem oldNode643 (p : Pattern) : eval read p 4392032 = NetHack.Sokoban12CostPartition.d643 p := by
  change eval read p 4392032 = (if p 160 then NetHack.Sokoban12CostPartition.d632 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 4392032 = .branch 160 3999633 3999641 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode632 p]
theorem oldNode644 (p : Pattern) : eval read p 4457788 = NetHack.Sokoban12CostPartition.d644 p := by
  change eval read p 4457788 = (if p 159 then NetHack.Sokoban12CostPartition.d633 p else NetHack.Sokoban12CostPartition.d643 p)
  have code : read 4457788 = .branch 159 4392032 4392030 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode643 p, oldNode633 p]
theorem oldNode645 (p : Pattern) : eval read p 4523442 = NetHack.Sokoban12CostPartition.d645 p := by
  change eval read p 4523442 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d644 p)
  have code : read 4523442 = .branch 158 4457788 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode644 p, oldNode599 p]
theorem oldNode646 (p : Pattern) : eval read p 4392033 = NetHack.Sokoban12CostPartition.d646 p := by
  change eval read p 4392033 = (if p 160 then NetHack.Sokoban12CostPartition.d637 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 4392033 = .branch 160 3999635 3999642 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode637 p]
theorem oldNode647 (p : Pattern) : eval read p 4457789 = NetHack.Sokoban12CostPartition.d647 p := by
  change eval read p 4457789 = (if p 159 then NetHack.Sokoban12CostPartition.d638 p else NetHack.Sokoban12CostPartition.d646 p)
  have code : read 4457789 = .branch 159 4392033 4392031 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode646 p, oldNode638 p]
end NetHack.Soko12Forward220.Shared
