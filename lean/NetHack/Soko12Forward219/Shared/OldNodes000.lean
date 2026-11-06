import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode0 (p : Pattern) : eval read p 0 = NetHack.Sokoban12CostPartition.d0 p := by
  change eval read p 0 = (0 : Int)
  exact eval_literal (by decide +kernel) p
theorem oldNode1 (p : Pattern) : eval read p 1 = NetHack.Sokoban12CostPartition.d1 p := by
  change eval read p 1 = (1 : Int)
  exact eval_literal (by decide +kernel) p
theorem oldNode2 (p : Pattern) : eval read p 2 = NetHack.Sokoban12CostPartition.d2 p := by
  change eval read p 2 = (2 : Int)
  exact eval_literal (by decide +kernel) p
theorem oldNode3 (p : Pattern) : eval read p 3 = NetHack.Sokoban12CostPartition.d3 p := by
  change eval read p 3 = (3 : Int)
  exact eval_literal (by decide +kernel) p
theorem oldNode4 (p : Pattern) : eval read p 4 = NetHack.Sokoban12CostPartition.d4 p := by
  change eval read p 4 = (4 : Int)
  exact eval_literal (by decide +kernel) p
theorem oldNode5 (p : Pattern) : eval read p 8192 = NetHack.Sokoban12CostPartition.d5 p := by
  change eval read p 8192 = (5 : Int)
  exact eval_literal literal5_checked p
theorem oldNode6 (p : Pattern) : eval read p 221184 = NetHack.Sokoban12CostPartition.d6 p := by
  change eval read p 221184 = (if p 193 then NetHack.Sokoban12CostPartition.d2 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 221184 = .branch 193 0 2 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode2 p]
theorem oldNode7 (p : Pattern) : eval read p 229376 = NetHack.Sokoban12CostPartition.d7 p := by
  change eval read p 229376 = (if p 192 then NetHack.Sokoban12CostPartition.d6 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 229376 = .branch 192 0 221184 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode6 p]
theorem oldNode8 (p : Pattern) : eval read p 90112 = NetHack.Sokoban12CostPartition.d8 p := by
  change eval read p 90112 = (if p 271 then NetHack.Sokoban12CostPartition.d1 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 90112 = .branch 271 0 1 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode1 p]
theorem oldNode9 (p : Pattern) : eval read p 90113 = NetHack.Sokoban12CostPartition.d9 p := by
  change eval read p 90113 = (if p 271 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 90113 = .branch 271 2 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode3 p]
theorem oldNode10 (p : Pattern) : eval read p 221185 = NetHack.Sokoban12CostPartition.d10 p := by
  change eval read p 221185 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 221185 = .branch 193 90112 90113 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode9 p]
theorem oldNode11 (p : Pattern) : eval read p 229377 = NetHack.Sokoban12CostPartition.d11 p := by
  change eval read p 229377 = (if p 192 then NetHack.Sokoban12CostPartition.d10 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 229377 = .branch 192 90112 221185 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode10 p]
theorem oldNode12 (p : Pattern) : eval read p 286720 = NetHack.Sokoban12CostPartition.d12 p := by
  change eval read p 286720 = (if p 168 then NetHack.Sokoban12CostPartition.d11 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 286720 = .branch 168 229376 229377 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode11 p]
theorem oldNode14 (p : Pattern) : eval read p 221186 = NetHack.Sokoban12CostPartition.d14 p := by
  change eval read p 221186 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 221186 = .branch 193 0 90113 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode9 p]
theorem oldNode15 (p : Pattern) : eval read p 229378 = NetHack.Sokoban12CostPartition.d15 p := by
  change eval read p 229378 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d14 p)
  have code : read 229378 = .branch 192 221186 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode14 p, oldNode3 p]
theorem oldNode16 (p : Pattern) : eval read p 90114 = NetHack.Sokoban12CostPartition.d16 p := by
  change eval read p 90114 = (if p 271 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 90114 = .branch 271 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode17 (p : Pattern) : eval read p 221187 = NetHack.Sokoban12CostPartition.d17 p := by
  change eval read p 221187 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 221187 = .branch 193 90114 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode3 p]
theorem oldNode18 (p : Pattern) : eval read p 229379 = NetHack.Sokoban12CostPartition.d18 p := by
  change eval read p 229379 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d17 p)
  have code : read 229379 = .branch 192 221187 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode17 p, oldNode3 p]
theorem oldNode19 (p : Pattern) : eval read p 286721 = NetHack.Sokoban12CostPartition.d19 p := by
  change eval read p 286721 = (if p 168 then NetHack.Sokoban12CostPartition.d18 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 286721 = .branch 168 229378 229379 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode18 p]
theorem oldNode21 (p : Pattern) : eval read p 286722 = NetHack.Sokoban12CostPartition.d21 p := by
  change eval read p 286722 = (if p 168 then NetHack.Sokoban12CostPartition.d15 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 286722 = .branch 168 229376 229378 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode15 p]
theorem oldNode22 (p : Pattern) : eval read p 286723 = NetHack.Sokoban12CostPartition.d22 p := by
  change eval read p 286723 = (if p 168 then NetHack.Sokoban12CostPartition.d18 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 286723 = .branch 168 229376 229379 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode18 p]
theorem oldNode24 (p : Pattern) : eval read p 229380 = NetHack.Sokoban12CostPartition.d24 p := by
  change eval read p 229380 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 229380 = .branch 192 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode25 (p : Pattern) : eval read p 229381 = NetHack.Sokoban12CostPartition.d25 p := by
  change eval read p 229381 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 229381 = .branch 192 90112 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode3 p]
theorem oldNode26 (p : Pattern) : eval read p 286724 = NetHack.Sokoban12CostPartition.d26 p := by
  change eval read p 286724 = (if p 168 then NetHack.Sokoban12CostPartition.d25 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 286724 = .branch 168 229380 229381 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode25 p]
end NetHack.Soko12Forward219.Shared
