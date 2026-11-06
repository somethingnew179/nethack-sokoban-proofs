import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode28 (p : Pattern) : eval read p 221188 = NetHack.Sokoban12CostPartition.d28 p := by
  change eval read p 221188 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 221188 = .branch 193 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode29 (p : Pattern) : eval read p 229382 = NetHack.Sokoban12CostPartition.d29 p := by
  change eval read p 229382 = (if p 192 then NetHack.Sokoban12CostPartition.d28 p else NetHack.Sokoban12CostPartition.d6 p)
  have code : read 229382 = .branch 192 221184 221188 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode6 p, oldNode28 p]
theorem oldNode30 (p : Pattern) : eval read p 229383 = NetHack.Sokoban12CostPartition.d30 p := by
  change eval read p 229383 = (if p 192 then NetHack.Sokoban12CostPartition.d28 p else NetHack.Sokoban12CostPartition.d14 p)
  have code : read 229383 = .branch 192 221186 221188 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode14 p, oldNode28 p]
theorem oldNode31 (p : Pattern) : eval read p 286725 = NetHack.Sokoban12CostPartition.d31 p := by
  change eval read p 286725 = (if p 168 then NetHack.Sokoban12CostPartition.d30 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 286725 = .branch 168 229382 229383 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode30 p]
theorem oldNode32 (p : Pattern) : eval read p 221189 = NetHack.Sokoban12CostPartition.d32 p := by
  change eval read p 221189 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 221189 = .branch 193 90112 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode3 p]
theorem oldNode33 (p : Pattern) : eval read p 286726 = NetHack.Sokoban12CostPartition.d33 p := by
  change eval read p 286726 = (if p 168 then NetHack.Sokoban12CostPartition.d32 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 286726 = .branch 168 229383 221189 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode32 p]
theorem oldNode35 (p : Pattern) : eval read p 90115 = NetHack.Sokoban12CostPartition.d35 p := by
  change eval read p 90115 = (if p 271 then NetHack.Sokoban12CostPartition.d2 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 90115 = .branch 271 0 2 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode2 p]
theorem oldNode36 (p : Pattern) : eval read p 221190 = NetHack.Sokoban12CostPartition.d36 p := by
  change eval read p 221190 = (if p 193 then NetHack.Sokoban12CostPartition.d35 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 221190 = .branch 193 0 90115 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode35 p]
theorem oldNode37 (p : Pattern) : eval read p 221191 = NetHack.Sokoban12CostPartition.d37 p := by
  change eval read p 221191 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 221191 = .branch 193 90114 90113 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode9 p]
theorem oldNode38 (p : Pattern) : eval read p 229384 = NetHack.Sokoban12CostPartition.d38 p := by
  change eval read p 229384 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d36 p)
  have code : read 229384 = .branch 192 221190 221191 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode36 p, oldNode37 p]
theorem oldNode39 (p : Pattern) : eval read p 221192 = NetHack.Sokoban12CostPartition.d39 p := by
  change eval read p 221192 = (if p 193 then NetHack.Sokoban12CostPartition.d16 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 221192 = .branch 193 0 90114 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode16 p]
theorem oldNode40 (p : Pattern) : eval read p 229385 = NetHack.Sokoban12CostPartition.d40 p := by
  change eval read p 229385 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d39 p)
  have code : read 229385 = .branch 192 221192 221191 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode39 p, oldNode37 p]
theorem oldNode41 (p : Pattern) : eval read p 286727 = NetHack.Sokoban12CostPartition.d41 p := by
  change eval read p 286727 = (if p 168 then NetHack.Sokoban12CostPartition.d40 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 286727 = .branch 168 229384 229385 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode40 p]
theorem oldNode42 (p : Pattern) : eval read p 229386 = NetHack.Sokoban12CostPartition.d42 p := by
  change eval read p 229386 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 229386 = .branch 192 90114 221191 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode37 p]
theorem oldNode43 (p : Pattern) : eval read p 286728 = NetHack.Sokoban12CostPartition.d43 p := by
  change eval read p 286728 = (if p 168 then NetHack.Sokoban12CostPartition.d42 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 286728 = .branch 168 229385 229386 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode42 p]
theorem oldNode54 (p : Pattern) : eval read p 221193 = NetHack.Sokoban12CostPartition.d54 p := by
  change eval read p 221193 = (if p 193 then NetHack.Sokoban12CostPartition.d4 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 221193 = .branch 193 2 4 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode4 p]
theorem oldNode55 (p : Pattern) : eval read p 229387 = NetHack.Sokoban12CostPartition.d55 p := by
  change eval read p 229387 = (if p 192 then NetHack.Sokoban12CostPartition.d54 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 229387 = .branch 192 2 221193 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode54 p]
theorem oldNode56 (p : Pattern) : eval read p 270337 = NetHack.Sokoban12CostPartition.d56 p := by
  change eval read p 270337 = (if p 186 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 270337 = .branch 186 229376 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode57 (p : Pattern) : eval read p 319489 = NetHack.Sokoban12CostPartition.d57 p := by
  change eval read p 319489 = (if p 160 then NetHack.Sokoban12CostPartition.d56 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 319489 = .branch 160 229376 270337 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode56 p]
theorem oldNode58 (p : Pattern) : eval read p 90116 = NetHack.Sokoban12CostPartition.d58 p := by
  change eval read p 90116 = (if p 271 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d4 p)
  have code : read 90116 = .branch 271 4 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode4 p, oldNode5 p]
theorem oldNode59 (p : Pattern) : eval read p 221194 = NetHack.Sokoban12CostPartition.d59 p := by
  change eval read p 221194 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 221194 = .branch 193 90113 90116 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode58 p]
theorem oldNode60 (p : Pattern) : eval read p 229388 = NetHack.Sokoban12CostPartition.d60 p := by
  change eval read p 229388 = (if p 192 then NetHack.Sokoban12CostPartition.d59 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 229388 = .branch 192 90113 221194 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode59 p]
theorem oldNode61 (p : Pattern) : eval read p 270338 = NetHack.Sokoban12CostPartition.d61 p := by
  change eval read p 270338 = (if p 186 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 270338 = .branch 186 229377 229388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode60 p]
theorem oldNode62 (p : Pattern) : eval read p 286729 = NetHack.Sokoban12CostPartition.d62 p := by
  change eval read p 286729 = (if p 168 then NetHack.Sokoban12CostPartition.d61 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 286729 = .branch 168 270337 270338 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode61 p]
end NetHack.Soko12Forward219.Shared
