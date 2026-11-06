import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode600 (p : Pattern) : eval read p 4392026 = NetHack.Sokoban12CostPartition.d600 p := by
  change eval read p 4392026 = (if p 160 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 4392026 = .branch 160 3999633 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode599 p]
theorem oldNode601 (p : Pattern) : eval read p 3671972 = NetHack.Sokoban12CostPartition.d601 p := by
  change eval read p 3671972 = (if p 187 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 3671972 = .branch 187 3411924 3411926 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode588 p]
theorem oldNode602 (p : Pattern) : eval read p 3737623 = NetHack.Sokoban12CostPartition.d602 p := by
  change eval read p 3737623 = (if p 186 then NetHack.Sokoban12CostPartition.d601 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 3737623 = .branch 186 3411924 3671972 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode601 p]
theorem oldNode603 (p : Pattern) : eval read p 3671973 = NetHack.Sokoban12CostPartition.d603 p := by
  change eval read p 3671973 = (if p 187 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 3671973 = .branch 187 3411925 3411927 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode590 p]
theorem oldNode604 (p : Pattern) : eval read p 3737624 = NetHack.Sokoban12CostPartition.d604 p := by
  change eval read p 3737624 = (if p 186 then NetHack.Sokoban12CostPartition.d603 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 3737624 = .branch 186 3411925 3671973 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode603 p]
theorem oldNode605 (p : Pattern) : eval read p 3999638 = NetHack.Sokoban12CostPartition.d605 p := by
  change eval read p 3999638 = (if p 168 then NetHack.Sokoban12CostPartition.d604 p else NetHack.Sokoban12CostPartition.d602 p)
  have code : read 3999638 = .branch 168 3737623 3737624 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode602 p, oldNode604 p]
theorem oldNode606 (p : Pattern) : eval read p 4392027 = NetHack.Sokoban12CostPartition.d606 p := by
  change eval read p 4392027 = (if p 160 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d605 p)
  have code : read 4392027 = .branch 160 3999638 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode605 p, oldNode599 p]
theorem oldNode607 (p : Pattern) : eval read p 4457784 = NetHack.Sokoban12CostPartition.d607 p := by
  change eval read p 4457784 = (if p 159 then NetHack.Sokoban12CostPartition.d606 p else NetHack.Sokoban12CostPartition.d600 p)
  have code : read 4457784 = .branch 159 4392026 4392027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode600 p, oldNode606 p]
theorem oldNode608 (p : Pattern) : eval read p 4523434 = NetHack.Sokoban12CostPartition.d608 p := by
  change eval read p 4523434 = (if p 158 then NetHack.Sokoban12CostPartition.d607 p else NetHack.Sokoban12CostPartition.d600 p)
  have code : read 4523434 = .branch 158 4392026 4457784 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode600 p, oldNode607 p]
theorem oldNode609 (p : Pattern) : eval read p 3999639 = NetHack.Sokoban12CostPartition.d609 p := by
  change eval read p 3999639 = (if p 168 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d590 p)
  have code : read 3999639 = .branch 168 3411927 3347243 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode590 p, oldNode594 p]
theorem oldNode610 (p : Pattern) : eval read p 4392028 = NetHack.Sokoban12CostPartition.d610 p := by
  change eval read p 4392028 = (if p 160 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 4392028 = .branch 160 3999635 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode609 p]
theorem oldNode611 (p : Pattern) : eval read p 3671974 = NetHack.Sokoban12CostPartition.d611 p := by
  change eval read p 3671974 = (if p 187 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 3671974 = .branch 187 3347242 3347243 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode594 p]
theorem oldNode612 (p : Pattern) : eval read p 3737625 = NetHack.Sokoban12CostPartition.d612 p := by
  change eval read p 3737625 = (if p 186 then NetHack.Sokoban12CostPartition.d611 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 3737625 = .branch 186 3347242 3671974 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode611 p]
theorem oldNode613 (p : Pattern) : eval read p 3999640 = NetHack.Sokoban12CostPartition.d613 p := by
  change eval read p 3999640 = (if p 168 then NetHack.Sokoban12CostPartition.d612 p else NetHack.Sokoban12CostPartition.d604 p)
  have code : read 3999640 = .branch 168 3737624 3737625 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode604 p, oldNode612 p]
theorem oldNode614 (p : Pattern) : eval read p 4392029 = NetHack.Sokoban12CostPartition.d614 p := by
  change eval read p 4392029 = (if p 160 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d613 p)
  have code : read 4392029 = .branch 160 3999640 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode613 p, oldNode609 p]
theorem oldNode615 (p : Pattern) : eval read p 4457785 = NetHack.Sokoban12CostPartition.d615 p := by
  change eval read p 4457785 = (if p 159 then NetHack.Sokoban12CostPartition.d614 p else NetHack.Sokoban12CostPartition.d610 p)
  have code : read 4457785 = .branch 159 4392028 4392029 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode610 p, oldNode614 p]
theorem oldNode616 (p : Pattern) : eval read p 4523435 = NetHack.Sokoban12CostPartition.d616 p := by
  change eval read p 4523435 = (if p 158 then NetHack.Sokoban12CostPartition.d615 p else NetHack.Sokoban12CostPartition.d610 p)
  have code : read 4523435 = .branch 158 4392028 4457785 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode610 p, oldNode615 p]
theorem oldNode617 (p : Pattern) : eval read p 4785024 = NetHack.Sokoban12CostPartition.d617 p := by
  change eval read p 4785024 = (if p 141 then NetHack.Sokoban12CostPartition.d616 p else NetHack.Sokoban12CostPartition.d608 p)
  have code : read 4785024 = .branch 141 4523434 4523435 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode608 p, oldNode616 p]
theorem oldNode618 (p : Pattern) : eval read p 4981435 = NetHack.Sokoban12CostPartition.d618 p := by
  change eval read p 4981435 = (if p 134 then NetHack.Sokoban12CostPartition.d617 p else NetHack.Sokoban12CostPartition.d598 p)
  have code : read 4981435 = .branch 134 4785023 4785024 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode598 p, oldNode617 p]
theorem oldNode619 (p : Pattern) : eval read p 4523436 = NetHack.Sokoban12CostPartition.d619 p := by
  change eval read p 4523436 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 4523436 = .branch 158 4392024 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode599 p]
theorem oldNode620 (p : Pattern) : eval read p 4523437 = NetHack.Sokoban12CostPartition.d620 p := by
  change eval read p 4523437 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 4523437 = .branch 158 4392025 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode609 p]
theorem oldNode621 (p : Pattern) : eval read p 4785025 = NetHack.Sokoban12CostPartition.d621 p := by
  change eval read p 4785025 = (if p 141 then NetHack.Sokoban12CostPartition.d620 p else NetHack.Sokoban12CostPartition.d619 p)
  have code : read 4785025 = .branch 141 4523436 4523437 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode619 p, oldNode620 p]
theorem oldNode622 (p : Pattern) : eval read p 4523438 = NetHack.Sokoban12CostPartition.d622 p := by
  change eval read p 4523438 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d607 p)
  have code : read 4523438 = .branch 158 4457784 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode607 p, oldNode599 p]
theorem oldNode623 (p : Pattern) : eval read p 4523439 = NetHack.Sokoban12CostPartition.d623 p := by
  change eval read p 4523439 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d615 p)
  have code : read 4523439 = .branch 158 4457785 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode615 p, oldNode609 p]
end NetHack.Soko12Forward220.Shared
