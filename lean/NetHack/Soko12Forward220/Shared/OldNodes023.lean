import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode696 (p : Pattern) : eval read p 4785033 = NetHack.Sokoban12CostPartition.d696 p := by
  change eval read p 4785033 = (if p 141 then NetHack.Sokoban12CostPartition.d695 p else NetHack.Sokoban12CostPartition.d694 p)
  have code : read 4785033 = .branch 141 4523448 4523449 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode694 p, oldNode695 p]
theorem oldNode697 (p : Pattern) : eval read p 4523450 = NetHack.Sokoban12CostPartition.d697 p := by
  change eval read p 4523450 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d682 p)
  have code : read 4523450 = .branch 158 4457790 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode682 p, oldNode674 p]
theorem oldNode698 (p : Pattern) : eval read p 4523451 = NetHack.Sokoban12CostPartition.d698 p := by
  change eval read p 4523451 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d690 p)
  have code : read 4523451 = .branch 158 4457791 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode690 p, oldNode684 p]
theorem oldNode699 (p : Pattern) : eval read p 4785034 = NetHack.Sokoban12CostPartition.d699 p := by
  change eval read p 4785034 = (if p 141 then NetHack.Sokoban12CostPartition.d698 p else NetHack.Sokoban12CostPartition.d697 p)
  have code : read 4785034 = .branch 141 4523450 4523451 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode697 p, oldNode698 p]
theorem oldNode700 (p : Pattern) : eval read p 4981441 = NetHack.Sokoban12CostPartition.d700 p := by
  change eval read p 4981441 = (if p 134 then NetHack.Sokoban12CostPartition.d699 p else NetHack.Sokoban12CostPartition.d696 p)
  have code : read 4981441 = .branch 134 4785033 4785034 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode696 p, oldNode699 p]
theorem oldNode701 (p : Pattern) : eval read p 5046778 = NetHack.Sokoban12CostPartition.d701 p := by
  change eval read p 5046778 = (if p 133 then NetHack.Sokoban12CostPartition.d700 p else NetHack.Sokoban12CostPartition.d693 p)
  have code : read 5046778 = .branch 133 4981440 4981441 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode693 p, oldNode700 p]
theorem oldNode702 (p : Pattern) : eval read p 4785035 = NetHack.Sokoban12CostPartition.d702 p := by
  change eval read p 4785035 = (if p 141 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d674 p)
  have code : read 4785035 = .branch 141 3999647 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode674 p, oldNode684 p]
theorem oldNode703 (p : Pattern) : eval read p 5046779 = NetHack.Sokoban12CostPartition.d703 p := by
  change eval read p 5046779 = (if p 133 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d700 p)
  have code : read 5046779 = .branch 133 4981441 4785035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode700 p, oldNode702 p]
theorem oldNode704 (p : Pattern) : eval read p 5112181 = NetHack.Sokoban12CostPartition.d704 p := by
  change eval read p 5112181 = (if p 132 then NetHack.Sokoban12CostPartition.d703 p else NetHack.Sokoban12CostPartition.d701 p)
  have code : read 5112181 = .branch 132 5046778 5046779 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode701 p, oldNode703 p]
theorem oldNode705 (p : Pattern) : eval read p 3737635 = NetHack.Sokoban12CostPartition.d705 p := by
  change eval read p 3737635 = (if p 186 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d676 p)
  have code : read 3737635 = .branch 186 3671975 3411930 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode676 p, oldNode662 p]
theorem oldNode706 (p : Pattern) : eval read p 3737636 = NetHack.Sokoban12CostPartition.d706 p := by
  change eval read p 3737636 = (if p 186 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d678 p)
  have code : read 3737636 = .branch 186 3671976 3411931 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode678 p, oldNode665 p]
theorem oldNode707 (p : Pattern) : eval read p 3999651 = NetHack.Sokoban12CostPartition.d707 p := by
  change eval read p 3999651 = (if p 168 then NetHack.Sokoban12CostPartition.d706 p else NetHack.Sokoban12CostPartition.d705 p)
  have code : read 3999651 = .branch 168 3737635 3737636 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode705 p, oldNode706 p]
theorem oldNode708 (p : Pattern) : eval read p 4392040 = NetHack.Sokoban12CostPartition.d708 p := by
  change eval read p 4392040 = (if p 160 then NetHack.Sokoban12CostPartition.d707 p else NetHack.Sokoban12CostPartition.d680 p)
  have code : read 4392040 = .branch 160 3999648 3999651 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode680 p, oldNode707 p]
theorem oldNode709 (p : Pattern) : eval read p 4457792 = NetHack.Sokoban12CostPartition.d709 p := by
  change eval read p 4457792 = (if p 159 then NetHack.Sokoban12CostPartition.d708 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 4457792 = .branch 159 4392034 4392040 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode708 p]
theorem oldNode710 (p : Pattern) : eval read p 4523452 = NetHack.Sokoban12CostPartition.d710 p := by
  change eval read p 4523452 = (if p 158 then NetHack.Sokoban12CostPartition.d709 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 4523452 = .branch 158 4392034 4457792 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode709 p]
theorem oldNode711 (p : Pattern) : eval read p 3737637 = NetHack.Sokoban12CostPartition.d711 p := by
  change eval read p 3737637 = (if p 186 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d686 p)
  have code : read 3737637 = .branch 186 3671977 3411933 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode686 p, oldNode669 p]
theorem oldNode712 (p : Pattern) : eval read p 3999652 = NetHack.Sokoban12CostPartition.d712 p := by
  change eval read p 3999652 = (if p 168 then NetHack.Sokoban12CostPartition.d711 p else NetHack.Sokoban12CostPartition.d706 p)
  have code : read 3999652 = .branch 168 3737636 3737637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode706 p, oldNode711 p]
theorem oldNode713 (p : Pattern) : eval read p 4392041 = NetHack.Sokoban12CostPartition.d713 p := by
  change eval read p 4392041 = (if p 160 then NetHack.Sokoban12CostPartition.d712 p else NetHack.Sokoban12CostPartition.d688 p)
  have code : read 4392041 = .branch 160 3999650 3999652 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode688 p, oldNode712 p]
theorem oldNode714 (p : Pattern) : eval read p 4457793 = NetHack.Sokoban12CostPartition.d714 p := by
  change eval read p 4457793 = (if p 159 then NetHack.Sokoban12CostPartition.d713 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 4457793 = .branch 159 4392035 4392041 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode713 p]
theorem oldNode715 (p : Pattern) : eval read p 4523453 = NetHack.Sokoban12CostPartition.d715 p := by
  change eval read p 4523453 = (if p 158 then NetHack.Sokoban12CostPartition.d714 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 4523453 = .branch 158 4392035 4457793 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode714 p]
theorem oldNode716 (p : Pattern) : eval read p 4785036 = NetHack.Sokoban12CostPartition.d716 p := by
  change eval read p 4785036 = (if p 141 then NetHack.Sokoban12CostPartition.d715 p else NetHack.Sokoban12CostPartition.d710 p)
  have code : read 4785036 = .branch 141 4523452 4523453 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode710 p, oldNode715 p]
theorem oldNode717 (p : Pattern) : eval read p 4981442 = NetHack.Sokoban12CostPartition.d717 p := by
  change eval read p 4981442 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d716 p)
  have code : read 4981442 = .branch 134 4785036 4785035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode716 p, oldNode702 p]
theorem oldNode718 (p : Pattern) : eval read p 4392042 = NetHack.Sokoban12CostPartition.d718 p := by
  change eval read p 4392042 = (if p 160 then NetHack.Sokoban12CostPartition.d707 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 4392042 = .branch 160 3999643 3999651 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode707 p]
theorem oldNode719 (p : Pattern) : eval read p 4457794 = NetHack.Sokoban12CostPartition.d719 p := by
  change eval read p 4457794 = (if p 159 then NetHack.Sokoban12CostPartition.d708 p else NetHack.Sokoban12CostPartition.d718 p)
  have code : read 4457794 = .branch 159 4392042 4392040 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode718 p, oldNode708 p]
end NetHack.Soko12Forward220.Shared
