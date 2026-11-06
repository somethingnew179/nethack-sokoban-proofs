import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode576 (p : Pattern) : eval read p 335965 = NetHack.Sokoban12CostPartition.d576 p := by
  change eval read p 335965 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d575 p)
  have code : read 335965 = .branch 158 327721 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode575 p, oldNode539 p]
theorem oldNode577 (p : Pattern) : eval read p 360507 = NetHack.Sokoban12CostPartition.d577 p := by
  change eval read p 360507 = (if p 141 then NetHack.Sokoban12CostPartition.d576 p else NetHack.Sokoban12CostPartition.d573 p)
  have code : read 360507 = .branch 141 335964 335965 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode573 p, oldNode576 p]
theorem oldNode578 (p : Pattern) : eval read p 368718 = NetHack.Sokoban12CostPartition.d578 p := by
  change eval read p 368718 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d577 p)
  have code : read 368718 = .branch 134 360507 360505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode577 p, oldNode557 p]
theorem oldNode579 (p : Pattern) : eval read p 376912 = NetHack.Sokoban12CostPartition.d579 p := by
  change eval read p 376912 = (if p 133 then NetHack.Sokoban12CostPartition.d578 p else NetHack.Sokoban12CostPartition.d570 p)
  have code : read 376912 = .branch 133 368717 368718 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode570 p, oldNode578 p]
theorem oldNode580 (p : Pattern) : eval read p 335966 = NetHack.Sokoban12CostPartition.d580 p := by
  change eval read p 335966 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d562 p)
  have code : read 335966 = .branch 158 327718 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode562 p, oldNode525 p]
theorem oldNode581 (p : Pattern) : eval read p 335967 = NetHack.Sokoban12CostPartition.d581 p := by
  change eval read p 335967 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d567 p)
  have code : read 335967 = .branch 158 327719 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode567 p, oldNode539 p]
theorem oldNode582 (p : Pattern) : eval read p 360508 = NetHack.Sokoban12CostPartition.d582 p := by
  change eval read p 360508 = (if p 141 then NetHack.Sokoban12CostPartition.d581 p else NetHack.Sokoban12CostPartition.d580 p)
  have code : read 360508 = .branch 141 335966 335967 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode580 p, oldNode581 p]
theorem oldNode583 (p : Pattern) : eval read p 368719 = NetHack.Sokoban12CostPartition.d583 p := by
  change eval read p 368719 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d582 p)
  have code : read 368719 = .branch 134 360508 360505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode582 p, oldNode557 p]
theorem oldNode584 (p : Pattern) : eval read p 376913 = NetHack.Sokoban12CostPartition.d584 p := by
  change eval read p 376913 = (if p 133 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d583 p)
  have code : read 376913 = .branch 133 368719 360505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode583 p, oldNode557 p]
theorem oldNode585 (p : Pattern) : eval read p 385071 = NetHack.Sokoban12CostPartition.d585 p := by
  change eval read p 385071 = (if p 132 then NetHack.Sokoban12CostPartition.d584 p else NetHack.Sokoban12CostPartition.d579 p)
  have code : read 385071 = .branch 132 376912 376913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode579 p, oldNode584 p]
theorem oldNode586 (p : Pattern) : eval read p 409625 = NetHack.Sokoban12CostPartition.d586 p := by
  change eval read p 409625 = (if p 108 then NetHack.Sokoban12CostPartition.d585 p else NetHack.Sokoban12CostPartition.d559 p)
  have code : read 409625 = .branch 108 385070 385071 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode559 p, oldNode585 p]
theorem oldNode587 (p : Pattern) : eval read p 221197 = NetHack.Sokoban12CostPartition.d587 p := by
  change eval read p 221197 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 221197 = .branch 193 2 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode588 (p : Pattern) : eval read p 229393 = NetHack.Sokoban12CostPartition.d588 p := by
  change eval read p 229393 = (if p 192 then NetHack.Sokoban12CostPartition.d587 p else NetHack.Sokoban12CostPartition.d54 p)
  have code : read 229393 = .branch 192 221193 221197 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode54 p, oldNode587 p]
theorem oldNode589 (p : Pattern) : eval read p 270357 = NetHack.Sokoban12CostPartition.d589 p := by
  change eval read p 270357 = (if p 186 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 270357 = .branch 186 229382 229393 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode588 p]
theorem oldNode590 (p : Pattern) : eval read p 229394 = NetHack.Sokoban12CostPartition.d590 p := by
  change eval read p 229394 = (if p 192 then NetHack.Sokoban12CostPartition.d587 p else NetHack.Sokoban12CostPartition.d259 p)
  have code : read 229394 = .branch 192 221195 221197 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode259 p, oldNode587 p]
theorem oldNode591 (p : Pattern) : eval read p 270358 = NetHack.Sokoban12CostPartition.d591 p := by
  change eval read p 270358 = (if p 186 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 270358 = .branch 186 229383 229394 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode590 p]
theorem oldNode592 (p : Pattern) : eval read p 286750 = NetHack.Sokoban12CostPartition.d592 p := by
  change eval read p 286750 = (if p 168 then NetHack.Sokoban12CostPartition.d591 p else NetHack.Sokoban12CostPartition.d589 p)
  have code : read 286750 = .branch 168 270357 270358 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode589 p, oldNode591 p]
theorem oldNode593 (p : Pattern) : eval read p 319540 = NetHack.Sokoban12CostPartition.d593 p := by
  change eval read p 319540 = (if p 160 then NetHack.Sokoban12CostPartition.d592 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 319540 = .branch 160 286725 286750 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode592 p]
theorem oldNode594 (p : Pattern) : eval read p 221198 = NetHack.Sokoban12CostPartition.d594 p := by
  change eval read p 221198 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 221198 = .branch 193 90113 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode5 p]
theorem oldNode595 (p : Pattern) : eval read p 270359 = NetHack.Sokoban12CostPartition.d595 p := by
  change eval read p 270359 = (if p 186 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 270359 = .branch 186 221189 221198 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode594 p]
theorem oldNode596 (p : Pattern) : eval read p 286751 = NetHack.Sokoban12CostPartition.d596 p := by
  change eval read p 286751 = (if p 168 then NetHack.Sokoban12CostPartition.d595 p else NetHack.Sokoban12CostPartition.d591 p)
  have code : read 286751 = .branch 168 270358 270359 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode591 p, oldNode595 p]
theorem oldNode597 (p : Pattern) : eval read p 319541 = NetHack.Sokoban12CostPartition.d597 p := by
  change eval read p 319541 = (if p 160 then NetHack.Sokoban12CostPartition.d596 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 319541 = .branch 160 286726 286751 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode596 p]
theorem oldNode598 (p : Pattern) : eval read p 360509 = NetHack.Sokoban12CostPartition.d598 p := by
  change eval read p 360509 = (if p 141 then NetHack.Sokoban12CostPartition.d597 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 360509 = .branch 141 319540 319541 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode597 p]
theorem oldNode599 (p : Pattern) : eval read p 286752 = NetHack.Sokoban12CostPartition.d599 p := by
  change eval read p 286752 = (if p 168 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d588 p)
  have code : read 286752 = .branch 168 229393 229394 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode588 p, oldNode590 p]
end NetHack.Soko12Forward219.Shared
