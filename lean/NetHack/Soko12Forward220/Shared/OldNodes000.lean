import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
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
theorem oldNode5 (p : Pattern) : eval read p 65536 = NetHack.Sokoban12CostPartition.d5 p := by
  change eval read p 65536 = (5 : Int)
  exact eval_literal literal5_checked p
theorem oldNode6 (p : Pattern) : eval read p 3347232 = NetHack.Sokoban12CostPartition.d6 p := by
  change eval read p 3347232 = (if p 193 then NetHack.Sokoban12CostPartition.d2 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3347232 = .branch 193 0 2 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode2 p]
theorem oldNode7 (p : Pattern) : eval read p 3411912 = NetHack.Sokoban12CostPartition.d7 p := by
  change eval read p 3411912 = (if p 192 then NetHack.Sokoban12CostPartition.d6 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3411912 = .branch 192 0 3347232 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode6 p]
theorem oldNode8 (p : Pattern) : eval read p 1638541 = NetHack.Sokoban12CostPartition.d8 p := by
  change eval read p 1638541 = (if p 271 then NetHack.Sokoban12CostPartition.d1 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 1638541 = .branch 271 0 1 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode1 p]
theorem oldNode9 (p : Pattern) : eval read p 1638542 = NetHack.Sokoban12CostPartition.d9 p := by
  change eval read p 1638542 = (if p 271 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 1638542 = .branch 271 2 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode3 p]
theorem oldNode10 (p : Pattern) : eval read p 3347234 = NetHack.Sokoban12CostPartition.d10 p := by
  change eval read p 3347234 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 3347234 = .branch 193 1638541 1638542 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode9 p]
theorem oldNode11 (p : Pattern) : eval read p 3411914 = NetHack.Sokoban12CostPartition.d11 p := by
  change eval read p 3411914 = (if p 192 then NetHack.Sokoban12CostPartition.d10 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 3411914 = .branch 192 1638541 3347234 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode10 p]
theorem oldNode12 (p : Pattern) : eval read p 3999607 = NetHack.Sokoban12CostPartition.d12 p := by
  change eval read p 3999607 = (if p 168 then NetHack.Sokoban12CostPartition.d11 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3999607 = .branch 168 3411912 3411914 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode11 p]
theorem oldNode14 (p : Pattern) : eval read p 3347236 = NetHack.Sokoban12CostPartition.d14 p := by
  change eval read p 3347236 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3347236 = .branch 193 0 1638542 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode9 p]
theorem oldNode15 (p : Pattern) : eval read p 3411916 = NetHack.Sokoban12CostPartition.d15 p := by
  change eval read p 3411916 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d14 p)
  have code : read 3411916 = .branch 192 3347236 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode14 p, oldNode3 p]
theorem oldNode16 (p : Pattern) : eval read p 1638544 = NetHack.Sokoban12CostPartition.d16 p := by
  change eval read p 1638544 = (if p 271 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 1638544 = .branch 271 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode17 (p : Pattern) : eval read p 3347237 = NetHack.Sokoban12CostPartition.d17 p := by
  change eval read p 3347237 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 3347237 = .branch 193 1638544 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode3 p]
theorem oldNode18 (p : Pattern) : eval read p 3411917 = NetHack.Sokoban12CostPartition.d18 p := by
  change eval read p 3411917 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d17 p)
  have code : read 3411917 = .branch 192 3347237 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode17 p, oldNode3 p]
theorem oldNode19 (p : Pattern) : eval read p 3999612 = NetHack.Sokoban12CostPartition.d19 p := by
  change eval read p 3999612 = (if p 168 then NetHack.Sokoban12CostPartition.d18 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 3999612 = .branch 168 3411916 3411917 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode18 p]
theorem oldNode21 (p : Pattern) : eval read p 3999617 = NetHack.Sokoban12CostPartition.d21 p := by
  change eval read p 3999617 = (if p 168 then NetHack.Sokoban12CostPartition.d15 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3999617 = .branch 168 3411912 3411916 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode15 p]
theorem oldNode22 (p : Pattern) : eval read p 3999619 = NetHack.Sokoban12CostPartition.d22 p := by
  change eval read p 3999619 = (if p 168 then NetHack.Sokoban12CostPartition.d18 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3999619 = .branch 168 3411912 3411917 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode18 p]
theorem oldNode24 (p : Pattern) : eval read p 3411920 = NetHack.Sokoban12CostPartition.d24 p := by
  change eval read p 3411920 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3411920 = .branch 192 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode25 (p : Pattern) : eval read p 3411922 = NetHack.Sokoban12CostPartition.d25 p := by
  change eval read p 3411922 = (if p 192 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 3411922 = .branch 192 1638541 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode3 p]
theorem oldNode26 (p : Pattern) : eval read p 3999628 = NetHack.Sokoban12CostPartition.d26 p := by
  change eval read p 3999628 = (if p 168 then NetHack.Sokoban12CostPartition.d25 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 3999628 = .branch 168 3411920 3411922 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode25 p]
end NetHack.Soko12Forward220.Shared
