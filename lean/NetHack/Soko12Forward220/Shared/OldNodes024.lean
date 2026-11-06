import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode720 (p : Pattern) : eval read p 4523454 = NetHack.Sokoban12CostPartition.d720 p := by
  change eval read p 4523454 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d719 p)
  have code : read 4523454 = .branch 158 4457794 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode719 p, oldNode674 p]
theorem oldNode721 (p : Pattern) : eval read p 4392043 = NetHack.Sokoban12CostPartition.d721 p := by
  change eval read p 4392043 = (if p 160 then NetHack.Sokoban12CostPartition.d712 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 4392043 = .branch 160 3999645 3999652 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode712 p]
theorem oldNode722 (p : Pattern) : eval read p 4457795 = NetHack.Sokoban12CostPartition.d722 p := by
  change eval read p 4457795 = (if p 159 then NetHack.Sokoban12CostPartition.d713 p else NetHack.Sokoban12CostPartition.d721 p)
  have code : read 4457795 = .branch 159 4392043 4392041 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode721 p, oldNode713 p]
theorem oldNode723 (p : Pattern) : eval read p 4523455 = NetHack.Sokoban12CostPartition.d723 p := by
  change eval read p 4523455 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d722 p)
  have code : read 4523455 = .branch 158 4457795 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode722 p, oldNode684 p]
theorem oldNode724 (p : Pattern) : eval read p 4785037 = NetHack.Sokoban12CostPartition.d724 p := by
  change eval read p 4785037 = (if p 141 then NetHack.Sokoban12CostPartition.d723 p else NetHack.Sokoban12CostPartition.d720 p)
  have code : read 4785037 = .branch 141 4523454 4523455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode720 p, oldNode723 p]
theorem oldNode725 (p : Pattern) : eval read p 4981443 = NetHack.Sokoban12CostPartition.d725 p := by
  change eval read p 4981443 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d724 p)
  have code : read 4981443 = .branch 134 4785037 4785035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode724 p, oldNode702 p]
theorem oldNode726 (p : Pattern) : eval read p 5046780 = NetHack.Sokoban12CostPartition.d726 p := by
  change eval read p 5046780 = (if p 133 then NetHack.Sokoban12CostPartition.d725 p else NetHack.Sokoban12CostPartition.d717 p)
  have code : read 5046780 = .branch 133 4981442 4981443 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode717 p, oldNode725 p]
theorem oldNode727 (p : Pattern) : eval read p 4523456 = NetHack.Sokoban12CostPartition.d727 p := by
  change eval read p 4523456 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d709 p)
  have code : read 4523456 = .branch 158 4457792 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode709 p, oldNode674 p]
theorem oldNode728 (p : Pattern) : eval read p 4523457 = NetHack.Sokoban12CostPartition.d728 p := by
  change eval read p 4523457 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d714 p)
  have code : read 4523457 = .branch 158 4457793 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode714 p, oldNode684 p]
theorem oldNode729 (p : Pattern) : eval read p 4785038 = NetHack.Sokoban12CostPartition.d729 p := by
  change eval read p 4785038 = (if p 141 then NetHack.Sokoban12CostPartition.d728 p else NetHack.Sokoban12CostPartition.d727 p)
  have code : read 4785038 = .branch 141 4523456 4523457 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode727 p, oldNode728 p]
theorem oldNode730 (p : Pattern) : eval read p 4981444 = NetHack.Sokoban12CostPartition.d730 p := by
  change eval read p 4981444 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d729 p)
  have code : read 4981444 = .branch 134 4785038 4785035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode729 p, oldNode702 p]
theorem oldNode731 (p : Pattern) : eval read p 5046781 = NetHack.Sokoban12CostPartition.d731 p := by
  change eval read p 5046781 = (if p 133 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d730 p)
  have code : read 5046781 = .branch 133 4981444 4785035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode730 p, oldNode702 p]
theorem oldNode732 (p : Pattern) : eval read p 5112182 = NetHack.Sokoban12CostPartition.d732 p := by
  change eval read p 5112182 = (if p 132 then NetHack.Sokoban12CostPartition.d731 p else NetHack.Sokoban12CostPartition.d726 p)
  have code : read 5112182 = .branch 132 5046780 5046781 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode726 p, oldNode731 p]
theorem oldNode733 (p : Pattern) : eval read p 5439701 = NetHack.Sokoban12CostPartition.d733 p := by
  change eval read p 5439701 = (if p 108 then NetHack.Sokoban12CostPartition.d732 p else NetHack.Sokoban12CostPartition.d704 p)
  have code : read 5439701 = .branch 108 5112181 5112182 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode704 p, oldNode732 p]
end NetHack.Soko12Forward220.Shared
