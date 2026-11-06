import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode720 (p : Pattern) : eval read p 335988 = NetHack.Sokoban12CostPartition.d720 p := by
  change eval read p 335988 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d719 p)
  have code : read 335988 = .branch 158 327732 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode719 p, oldNode674 p]
theorem oldNode721 (p : Pattern) : eval read p 319559 = NetHack.Sokoban12CostPartition.d721 p := by
  change eval read p 319559 = (if p 160 then NetHack.Sokoban12CostPartition.d712 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 319559 = .branch 160 286728 286765 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode712 p]
theorem oldNode722 (p : Pattern) : eval read p 327733 = NetHack.Sokoban12CostPartition.d722 p := by
  change eval read p 327733 = (if p 159 then NetHack.Sokoban12CostPartition.d713 p else NetHack.Sokoban12CostPartition.d721 p)
  have code : read 327733 = .branch 159 319559 319557 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode721 p, oldNode713 p]
theorem oldNode723 (p : Pattern) : eval read p 335989 = NetHack.Sokoban12CostPartition.d723 p := by
  change eval read p 335989 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d722 p)
  have code : read 335989 = .branch 158 327733 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode722 p, oldNode684 p]
theorem oldNode724 (p : Pattern) : eval read p 360523 = NetHack.Sokoban12CostPartition.d724 p := by
  change eval read p 360523 = (if p 141 then NetHack.Sokoban12CostPartition.d723 p else NetHack.Sokoban12CostPartition.d720 p)
  have code : read 360523 = .branch 141 335988 335989 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode720 p, oldNode723 p]
theorem oldNode725 (p : Pattern) : eval read p 368728 = NetHack.Sokoban12CostPartition.d725 p := by
  change eval read p 368728 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d724 p)
  have code : read 368728 = .branch 134 360523 360521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode724 p, oldNode702 p]
theorem oldNode726 (p : Pattern) : eval read p 376920 = NetHack.Sokoban12CostPartition.d726 p := by
  change eval read p 376920 = (if p 133 then NetHack.Sokoban12CostPartition.d725 p else NetHack.Sokoban12CostPartition.d717 p)
  have code : read 376920 = .branch 133 368727 368728 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode717 p, oldNode725 p]
theorem oldNode727 (p : Pattern) : eval read p 335990 = NetHack.Sokoban12CostPartition.d727 p := by
  change eval read p 335990 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d709 p)
  have code : read 335990 = .branch 158 327730 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode709 p, oldNode674 p]
theorem oldNode728 (p : Pattern) : eval read p 335991 = NetHack.Sokoban12CostPartition.d728 p := by
  change eval read p 335991 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d714 p)
  have code : read 335991 = .branch 158 327731 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode714 p, oldNode684 p]
theorem oldNode729 (p : Pattern) : eval read p 360524 = NetHack.Sokoban12CostPartition.d729 p := by
  change eval read p 360524 = (if p 141 then NetHack.Sokoban12CostPartition.d728 p else NetHack.Sokoban12CostPartition.d727 p)
  have code : read 360524 = .branch 141 335990 335991 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode727 p, oldNode728 p]
theorem oldNode730 (p : Pattern) : eval read p 368729 = NetHack.Sokoban12CostPartition.d730 p := by
  change eval read p 368729 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d729 p)
  have code : read 368729 = .branch 134 360524 360521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode729 p, oldNode702 p]
theorem oldNode731 (p : Pattern) : eval read p 376921 = NetHack.Sokoban12CostPartition.d731 p := by
  change eval read p 376921 = (if p 133 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d730 p)
  have code : read 376921 = .branch 133 368729 360521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode730 p, oldNode702 p]
theorem oldNode732 (p : Pattern) : eval read p 385075 = NetHack.Sokoban12CostPartition.d732 p := by
  change eval read p 385075 = (if p 132 then NetHack.Sokoban12CostPartition.d731 p else NetHack.Sokoban12CostPartition.d726 p)
  have code : read 385075 = .branch 132 376920 376921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode726 p, oldNode731 p]
theorem oldNode733 (p : Pattern) : eval read p 409627 = NetHack.Sokoban12CostPartition.d733 p := by
  change eval read p 409627 = (if p 108 then NetHack.Sokoban12CostPartition.d732 p else NetHack.Sokoban12CostPartition.d704 p)
  have code : read 409627 = .branch 108 385074 385075 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode704 p, oldNode732 p]
end NetHack.Soko12Forward219.Shared
