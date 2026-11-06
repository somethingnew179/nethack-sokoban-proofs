import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode624 (p : Pattern) : eval read p 360512 = NetHack.Sokoban12CostPartition.d624 p := by
  change eval read p 360512 = (if p 141 then NetHack.Sokoban12CostPartition.d623 p else NetHack.Sokoban12CostPartition.d622 p)
  have code : read 360512 = .branch 141 335972 335973 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode622 p, oldNode623 p]
theorem oldNode625 (p : Pattern) : eval read p 368721 = NetHack.Sokoban12CostPartition.d625 p := by
  change eval read p 368721 = (if p 134 then NetHack.Sokoban12CostPartition.d624 p else NetHack.Sokoban12CostPartition.d621 p)
  have code : read 368721 = .branch 134 360511 360512 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode621 p, oldNode624 p]
theorem oldNode626 (p : Pattern) : eval read p 376914 = NetHack.Sokoban12CostPartition.d626 p := by
  change eval read p 376914 = (if p 133 then NetHack.Sokoban12CostPartition.d625 p else NetHack.Sokoban12CostPartition.d618 p)
  have code : read 376914 = .branch 133 368720 368721 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode618 p, oldNode625 p]
theorem oldNode627 (p : Pattern) : eval read p 360513 = NetHack.Sokoban12CostPartition.d627 p := by
  change eval read p 360513 = (if p 141 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d599 p)
  have code : read 360513 = .branch 141 286752 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode599 p, oldNode609 p]
theorem oldNode628 (p : Pattern) : eval read p 376915 = NetHack.Sokoban12CostPartition.d628 p := by
  change eval read p 376915 = (if p 133 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d625 p)
  have code : read 376915 = .branch 133 368721 360513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode625 p, oldNode627 p]
theorem oldNode629 (p : Pattern) : eval read p 385072 = NetHack.Sokoban12CostPartition.d629 p := by
  change eval read p 385072 = (if p 132 then NetHack.Sokoban12CostPartition.d628 p else NetHack.Sokoban12CostPartition.d626 p)
  have code : read 385072 = .branch 132 376914 376915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode626 p, oldNode628 p]
theorem oldNode630 (p : Pattern) : eval read p 270363 = NetHack.Sokoban12CostPartition.d630 p := by
  change eval read p 270363 = (if p 186 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d601 p)
  have code : read 270363 = .branch 186 262151 229393 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode601 p, oldNode588 p]
theorem oldNode631 (p : Pattern) : eval read p 270364 = NetHack.Sokoban12CostPartition.d631 p := by
  change eval read p 270364 = (if p 186 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d603 p)
  have code : read 270364 = .branch 186 262152 229394 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode603 p, oldNode590 p]
theorem oldNode632 (p : Pattern) : eval read p 286756 = NetHack.Sokoban12CostPartition.d632 p := by
  change eval read p 286756 = (if p 168 then NetHack.Sokoban12CostPartition.d631 p else NetHack.Sokoban12CostPartition.d630 p)
  have code : read 286756 = .branch 168 270363 270364 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode630 p, oldNode631 p]
theorem oldNode633 (p : Pattern) : eval read p 319546 = NetHack.Sokoban12CostPartition.d633 p := by
  change eval read p 319546 = (if p 160 then NetHack.Sokoban12CostPartition.d632 p else NetHack.Sokoban12CostPartition.d605 p)
  have code : read 319546 = .branch 160 286753 286756 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode605 p, oldNode632 p]
theorem oldNode634 (p : Pattern) : eval read p 327724 = NetHack.Sokoban12CostPartition.d634 p := by
  change eval read p 327724 = (if p 159 then NetHack.Sokoban12CostPartition.d633 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 327724 = .branch 159 319540 319546 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode633 p]
theorem oldNode635 (p : Pattern) : eval read p 335974 = NetHack.Sokoban12CostPartition.d635 p := by
  change eval read p 335974 = (if p 158 then NetHack.Sokoban12CostPartition.d634 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 335974 = .branch 158 319540 327724 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode634 p]
theorem oldNode636 (p : Pattern) : eval read p 270365 = NetHack.Sokoban12CostPartition.d636 p := by
  change eval read p 270365 = (if p 186 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d611 p)
  have code : read 270365 = .branch 186 262153 221198 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode611 p, oldNode594 p]
theorem oldNode637 (p : Pattern) : eval read p 286757 = NetHack.Sokoban12CostPartition.d637 p := by
  change eval read p 286757 = (if p 168 then NetHack.Sokoban12CostPartition.d636 p else NetHack.Sokoban12CostPartition.d631 p)
  have code : read 286757 = .branch 168 270364 270365 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode631 p, oldNode636 p]
theorem oldNode638 (p : Pattern) : eval read p 319547 = NetHack.Sokoban12CostPartition.d638 p := by
  change eval read p 319547 = (if p 160 then NetHack.Sokoban12CostPartition.d637 p else NetHack.Sokoban12CostPartition.d613 p)
  have code : read 319547 = .branch 160 286755 286757 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode613 p, oldNode637 p]
theorem oldNode639 (p : Pattern) : eval read p 327725 = NetHack.Sokoban12CostPartition.d639 p := by
  change eval read p 327725 = (if p 159 then NetHack.Sokoban12CostPartition.d638 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 327725 = .branch 159 319541 319547 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode638 p]
theorem oldNode640 (p : Pattern) : eval read p 335975 = NetHack.Sokoban12CostPartition.d640 p := by
  change eval read p 335975 = (if p 158 then NetHack.Sokoban12CostPartition.d639 p else NetHack.Sokoban12CostPartition.d597 p)
  have code : read 335975 = .branch 158 319541 327725 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode597 p, oldNode639 p]
theorem oldNode641 (p : Pattern) : eval read p 360514 = NetHack.Sokoban12CostPartition.d641 p := by
  change eval read p 360514 = (if p 141 then NetHack.Sokoban12CostPartition.d640 p else NetHack.Sokoban12CostPartition.d635 p)
  have code : read 360514 = .branch 141 335974 335975 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode635 p, oldNode640 p]
theorem oldNode642 (p : Pattern) : eval read p 368722 = NetHack.Sokoban12CostPartition.d642 p := by
  change eval read p 368722 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d641 p)
  have code : read 368722 = .branch 134 360514 360513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode641 p, oldNode627 p]
theorem oldNode643 (p : Pattern) : eval read p 319548 = NetHack.Sokoban12CostPartition.d643 p := by
  change eval read p 319548 = (if p 160 then NetHack.Sokoban12CostPartition.d632 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 319548 = .branch 160 286725 286756 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode632 p]
theorem oldNode644 (p : Pattern) : eval read p 327726 = NetHack.Sokoban12CostPartition.d644 p := by
  change eval read p 327726 = (if p 159 then NetHack.Sokoban12CostPartition.d633 p else NetHack.Sokoban12CostPartition.d643 p)
  have code : read 327726 = .branch 159 319548 319546 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode643 p, oldNode633 p]
theorem oldNode645 (p : Pattern) : eval read p 335976 = NetHack.Sokoban12CostPartition.d645 p := by
  change eval read p 335976 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d644 p)
  have code : read 335976 = .branch 158 327726 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode644 p, oldNode599 p]
theorem oldNode646 (p : Pattern) : eval read p 319549 = NetHack.Sokoban12CostPartition.d646 p := by
  change eval read p 319549 = (if p 160 then NetHack.Sokoban12CostPartition.d637 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 319549 = .branch 160 286726 286757 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode637 p]
theorem oldNode647 (p : Pattern) : eval read p 327727 = NetHack.Sokoban12CostPartition.d647 p := by
  change eval read p 327727 = (if p 159 then NetHack.Sokoban12CostPartition.d638 p else NetHack.Sokoban12CostPartition.d646 p)
  have code : read 327727 = .branch 159 319549 319547 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode646 p, oldNode638 p]
end NetHack.Soko12Forward219.Shared
