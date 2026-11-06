import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode648 (p : Pattern) : eval read p 335977 = NetHack.Sokoban12CostPartition.d648 p := by
  change eval read p 335977 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d647 p)
  have code : read 335977 = .branch 158 327727 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode647 p, oldNode609 p]
theorem oldNode649 (p : Pattern) : eval read p 360515 = NetHack.Sokoban12CostPartition.d649 p := by
  change eval read p 360515 = (if p 141 then NetHack.Sokoban12CostPartition.d648 p else NetHack.Sokoban12CostPartition.d645 p)
  have code : read 360515 = .branch 141 335976 335977 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode645 p, oldNode648 p]
theorem oldNode650 (p : Pattern) : eval read p 368723 = NetHack.Sokoban12CostPartition.d650 p := by
  change eval read p 368723 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d649 p)
  have code : read 368723 = .branch 134 360515 360513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode649 p, oldNode627 p]
theorem oldNode651 (p : Pattern) : eval read p 376916 = NetHack.Sokoban12CostPartition.d651 p := by
  change eval read p 376916 = (if p 133 then NetHack.Sokoban12CostPartition.d650 p else NetHack.Sokoban12CostPartition.d642 p)
  have code : read 376916 = .branch 133 368722 368723 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode642 p, oldNode650 p]
theorem oldNode652 (p : Pattern) : eval read p 335978 = NetHack.Sokoban12CostPartition.d652 p := by
  change eval read p 335978 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d634 p)
  have code : read 335978 = .branch 158 327724 286752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode634 p, oldNode599 p]
theorem oldNode653 (p : Pattern) : eval read p 335979 = NetHack.Sokoban12CostPartition.d653 p := by
  change eval read p 335979 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d639 p)
  have code : read 335979 = .branch 158 327725 286754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode639 p, oldNode609 p]
theorem oldNode654 (p : Pattern) : eval read p 360516 = NetHack.Sokoban12CostPartition.d654 p := by
  change eval read p 360516 = (if p 141 then NetHack.Sokoban12CostPartition.d653 p else NetHack.Sokoban12CostPartition.d652 p)
  have code : read 360516 = .branch 141 335978 335979 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode652 p, oldNode653 p]
theorem oldNode655 (p : Pattern) : eval read p 368724 = NetHack.Sokoban12CostPartition.d655 p := by
  change eval read p 368724 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d654 p)
  have code : read 368724 = .branch 134 360516 360513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode654 p, oldNode627 p]
theorem oldNode656 (p : Pattern) : eval read p 376917 = NetHack.Sokoban12CostPartition.d656 p := by
  change eval read p 376917 = (if p 133 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d655 p)
  have code : read 376917 = .branch 133 368724 360513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode655 p, oldNode627 p]
theorem oldNode657 (p : Pattern) : eval read p 385073 = NetHack.Sokoban12CostPartition.d657 p := by
  change eval read p 385073 = (if p 132 then NetHack.Sokoban12CostPartition.d656 p else NetHack.Sokoban12CostPartition.d651 p)
  have code : read 385073 = .branch 132 376916 376917 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode651 p, oldNode656 p]
theorem oldNode658 (p : Pattern) : eval read p 409626 = NetHack.Sokoban12CostPartition.d658 p := by
  change eval read p 409626 = (if p 108 then NetHack.Sokoban12CostPartition.d657 p else NetHack.Sokoban12CostPartition.d629 p)
  have code : read 409626 = .branch 108 385072 385073 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode629 p, oldNode657 p]
theorem oldNode659 (p : Pattern) : eval read p 90118 = NetHack.Sokoban12CostPartition.d659 p := by
  change eval read p 90118 = (if p 271 then NetHack.Sokoban12CostPartition.d4 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 90118 = .branch 271 2 4 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode4 p]
theorem oldNode660 (p : Pattern) : eval read p 221199 = NetHack.Sokoban12CostPartition.d660 p := by
  change eval read p 221199 = (if p 193 then NetHack.Sokoban12CostPartition.d659 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 221199 = .branch 193 2 90118 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode659 p]
theorem oldNode661 (p : Pattern) : eval read p 221200 = NetHack.Sokoban12CostPartition.d661 p := by
  change eval read p 221200 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 221200 = .branch 193 90117 90116 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode58 p]
theorem oldNode662 (p : Pattern) : eval read p 229395 = NetHack.Sokoban12CostPartition.d662 p := by
  change eval read p 229395 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d660 p)
  have code : read 229395 = .branch 192 221199 221200 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode660 p, oldNode661 p]
theorem oldNode663 (p : Pattern) : eval read p 270366 = NetHack.Sokoban12CostPartition.d663 p := by
  change eval read p 270366 = (if p 186 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 270366 = .branch 186 229384 229395 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode662 p]
theorem oldNode664 (p : Pattern) : eval read p 221201 = NetHack.Sokoban12CostPartition.d664 p := by
  change eval read p 221201 = (if p 193 then NetHack.Sokoban12CostPartition.d262 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 221201 = .branch 193 2 90117 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode262 p]
theorem oldNode665 (p : Pattern) : eval read p 229396 = NetHack.Sokoban12CostPartition.d665 p := by
  change eval read p 229396 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d664 p)
  have code : read 229396 = .branch 192 221201 221200 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode664 p, oldNode661 p]
theorem oldNode666 (p : Pattern) : eval read p 270367 = NetHack.Sokoban12CostPartition.d666 p := by
  change eval read p 270367 = (if p 186 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 270367 = .branch 186 229385 229396 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode665 p]
theorem oldNode667 (p : Pattern) : eval read p 286758 = NetHack.Sokoban12CostPartition.d667 p := by
  change eval read p 286758 = (if p 168 then NetHack.Sokoban12CostPartition.d666 p else NetHack.Sokoban12CostPartition.d663 p)
  have code : read 286758 = .branch 168 270366 270367 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode663 p, oldNode666 p]
theorem oldNode668 (p : Pattern) : eval read p 319550 = NetHack.Sokoban12CostPartition.d668 p := by
  change eval read p 319550 = (if p 160 then NetHack.Sokoban12CostPartition.d667 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 319550 = .branch 160 286727 286758 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode667 p]
theorem oldNode669 (p : Pattern) : eval read p 229397 = NetHack.Sokoban12CostPartition.d669 p := by
  change eval read p 229397 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 229397 = .branch 192 90117 221200 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode661 p]
theorem oldNode670 (p : Pattern) : eval read p 270368 = NetHack.Sokoban12CostPartition.d670 p := by
  change eval read p 270368 = (if p 186 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 270368 = .branch 186 229386 229397 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode669 p]
theorem oldNode671 (p : Pattern) : eval read p 286759 = NetHack.Sokoban12CostPartition.d671 p := by
  change eval read p 286759 = (if p 168 then NetHack.Sokoban12CostPartition.d670 p else NetHack.Sokoban12CostPartition.d666 p)
  have code : read 286759 = .branch 168 270367 270368 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode666 p, oldNode670 p]
end NetHack.Soko12Forward219.Shared
