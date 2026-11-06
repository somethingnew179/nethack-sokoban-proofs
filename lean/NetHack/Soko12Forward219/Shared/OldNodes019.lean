import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode600 (p : Pattern) : eval read p 319542 = NetHack.Sokoban12CostPartition.d600 p := by
  change eval read p 319542 = (if p 160 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 319542 = .branch 160 286725 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode599 p]
theorem oldNode601 (p : Pattern) : eval read p 262151 = NetHack.Sokoban12CostPartition.d601 p := by
  change eval read p 262151 = (if p 187 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 262151 = .branch 187 229382 229393 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode588 p]
theorem oldNode602 (p : Pattern) : eval read p 270360 = NetHack.Sokoban12CostPartition.d602 p := by
  change eval read p 270360 = (if p 186 then NetHack.Sokoban12CostPartition.d601 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 270360 = .branch 186 229382 262151 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode601 p]
theorem oldNode603 (p : Pattern) : eval read p 262152 = NetHack.Sokoban12CostPartition.d603 p := by
  change eval read p 262152 = (if p 187 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 262152 = .branch 187 229383 229394 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode590 p]
theorem oldNode604 (p : Pattern) : eval read p 270361 = NetHack.Sokoban12CostPartition.d604 p := by
  change eval read p 270361 = (if p 186 then NetHack.Sokoban12CostPartition.d603 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 270361 = .branch 186 229383 262152 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode603 p]
theorem oldNode605 (p : Pattern) : eval read p 286753 = NetHack.Sokoban12CostPartition.d605 p := by
  change eval read p 286753 = (if p 168 then NetHack.Sokoban12CostPartition.d604 p else NetHack.Sokoban12CostPartition.d602 p)
  have code : read 286753 = .branch 168 270360 270361 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode602 p, oldNode604 p]
theorem oldNode606 (p : Pattern) : eval read p 319543 = NetHack.Sokoban12CostPartition.d606 p := by
  change eval read p 319543 = (if p 160 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d605 p)
  have code : read 319543 = .branch 160 286753 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode605 p, oldNode599 p]
theorem oldNode607 (p : Pattern) : eval read p 327722 = NetHack.Sokoban12CostPartition.d607 p := by
  change eval read p 327722 = (if p 159 then NetHack.Sokoban12CostPartition.d606 p else NetHack.Sokoban12CostPartition.d600 p)
  have code : read 327722 = .branch 159 319542 319543 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode600 p, oldNode606 p]
theorem oldNode608 (p : Pattern) : eval read p 335968 = NetHack.Sokoban12CostPartition.d608 p := by
  change eval read p 335968 = (if p 158 then NetHack.Sokoban12CostPartition.d607 p else NetHack.Sokoban12CostPartition.d600 p)
  have code : read 335968 = .branch 158 319542 327722 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode600 p, oldNode607 p]
theorem oldNode609 (p : Pattern) : eval read p 286754 = NetHack.Sokoban12CostPartition.d609 p := by
  change eval read p 286754 = (if p 168 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d590 p)
  have code : read 286754 = .branch 168 229394 221198 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode590 p, oldNode594 p]
theorem oldNode610 (p : Pattern) : eval read p 319544 = NetHack.Sokoban12CostPartition.d610 p := by
  change eval read p 319544 = (if p 160 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 319544 = .branch 160 286726 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode609 p]
theorem oldNode611 (p : Pattern) : eval read p 262153 = NetHack.Sokoban12CostPartition.d611 p := by
  change eval read p 262153 = (if p 187 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 262153 = .branch 187 221189 221198 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode594 p]
theorem oldNode612 (p : Pattern) : eval read p 270362 = NetHack.Sokoban12CostPartition.d612 p := by
  change eval read p 270362 = (if p 186 then NetHack.Sokoban12CostPartition.d611 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 270362 = .branch 186 221189 262153 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode611 p]
theorem oldNode613 (p : Pattern) : eval read p 286755 = NetHack.Sokoban12CostPartition.d613 p := by
  change eval read p 286755 = (if p 168 then NetHack.Sokoban12CostPartition.d612 p else NetHack.Sokoban12CostPartition.d604 p)
  have code : read 286755 = .branch 168 270361 270362 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode604 p, oldNode612 p]
theorem oldNode614 (p : Pattern) : eval read p 319545 = NetHack.Sokoban12CostPartition.d614 p := by
  change eval read p 319545 = (if p 160 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d613 p)
  have code : read 319545 = .branch 160 286755 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode613 p, oldNode609 p]
theorem oldNode615 (p : Pattern) : eval read p 327723 = NetHack.Sokoban12CostPartition.d615 p := by
  change eval read p 327723 = (if p 159 then NetHack.Sokoban12CostPartition.d614 p else NetHack.Sokoban12CostPartition.d610 p)
  have code : read 327723 = .branch 159 319544 319545 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode610 p, oldNode614 p]
theorem oldNode616 (p : Pattern) : eval read p 335969 = NetHack.Sokoban12CostPartition.d616 p := by
  change eval read p 335969 = (if p 158 then NetHack.Sokoban12CostPartition.d615 p else NetHack.Sokoban12CostPartition.d610 p)
  have code : read 335969 = .branch 158 319544 327723 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode610 p, oldNode615 p]
theorem oldNode617 (p : Pattern) : eval read p 360510 = NetHack.Sokoban12CostPartition.d617 p := by
  change eval read p 360510 = (if p 141 then NetHack.Sokoban12CostPartition.d616 p else NetHack.Sokoban12CostPartition.d608 p)
  have code : read 360510 = .branch 141 335968 335969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode608 p, oldNode616 p]
theorem oldNode618 (p : Pattern) : eval read p 368720 = NetHack.Sokoban12CostPartition.d618 p := by
  change eval read p 368720 = (if p 134 then NetHack.Sokoban12CostPartition.d617 p else NetHack.Sokoban12CostPartition.d598 p)
  have code : read 368720 = .branch 134 360509 360510 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode598 p, oldNode617 p]
theorem oldNode619 (p : Pattern) : eval read p 335970 = NetHack.Sokoban12CostPartition.d619 p := by
  change eval read p 335970 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 335970 = .branch 158 319540 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode599 p]
theorem oldNode620 (p : Pattern) : eval read p 335971 = NetHack.Sokoban12CostPartition.d620 p := by
  change eval read p 335971 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 335971 = .branch 158 319541 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode609 p]
theorem oldNode621 (p : Pattern) : eval read p 360511 = NetHack.Sokoban12CostPartition.d621 p := by
  change eval read p 360511 = (if p 141 then NetHack.Sokoban12CostPartition.d620 p else NetHack.Sokoban12CostPartition.d619 p)
  have code : read 360511 = .branch 141 335970 335971 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode619 p, oldNode620 p]
theorem oldNode622 (p : Pattern) : eval read p 335972 = NetHack.Sokoban12CostPartition.d622 p := by
  change eval read p 335972 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d607 p)
  have code : read 335972 = .branch 158 327722 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode607 p, oldNode599 p]
theorem oldNode623 (p : Pattern) : eval read p 335973 = NetHack.Sokoban12CostPartition.d623 p := by
  change eval read p 335973 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d615 p)
  have code : read 335973 = .branch 158 327723 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode615 p, oldNode609 p]
end NetHack.Soko12Forward219.Shared
