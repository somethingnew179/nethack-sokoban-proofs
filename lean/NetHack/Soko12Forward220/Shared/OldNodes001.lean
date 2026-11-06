import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode28 (p : Pattern) : eval read p 3347240 = NetHack.Sokoban12CostPartition.d28 p := by
  change eval read p 3347240 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3347240 = .branch 193 0 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode3 p]
theorem oldNode29 (p : Pattern) : eval read p 3411924 = NetHack.Sokoban12CostPartition.d29 p := by
  change eval read p 3411924 = (if p 192 then NetHack.Sokoban12CostPartition.d28 p else NetHack.Sokoban12CostPartition.d6 p)
  have code : read 3411924 = .branch 192 3347232 3347240 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode6 p, oldNode28 p]
theorem oldNode30 (p : Pattern) : eval read p 3411925 = NetHack.Sokoban12CostPartition.d30 p := by
  change eval read p 3411925 = (if p 192 then NetHack.Sokoban12CostPartition.d28 p else NetHack.Sokoban12CostPartition.d14 p)
  have code : read 3411925 = .branch 192 3347236 3347240 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode14 p, oldNode28 p]
theorem oldNode31 (p : Pattern) : eval read p 3999633 = NetHack.Sokoban12CostPartition.d31 p := by
  change eval read p 3999633 = (if p 168 then NetHack.Sokoban12CostPartition.d30 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 3999633 = .branch 168 3411924 3411925 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode30 p]
theorem oldNode32 (p : Pattern) : eval read p 3347242 = NetHack.Sokoban12CostPartition.d32 p := by
  change eval read p 3347242 = (if p 193 then NetHack.Sokoban12CostPartition.d3 p else NetHack.Sokoban12CostPartition.d8 p)
  have code : read 3347242 = .branch 193 1638541 3 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode8 p, oldNode3 p]
theorem oldNode33 (p : Pattern) : eval read p 3999635 = NetHack.Sokoban12CostPartition.d33 p := by
  change eval read p 3999635 = (if p 168 then NetHack.Sokoban12CostPartition.d32 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 3999635 = .branch 168 3411925 3347242 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode32 p]
theorem oldNode35 (p : Pattern) : eval read p 1638546 = NetHack.Sokoban12CostPartition.d35 p := by
  change eval read p 1638546 = (if p 271 then NetHack.Sokoban12CostPartition.d2 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 1638546 = .branch 271 0 2 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode2 p]
theorem oldNode36 (p : Pattern) : eval read p 3347244 = NetHack.Sokoban12CostPartition.d36 p := by
  change eval read p 3347244 = (if p 193 then NetHack.Sokoban12CostPartition.d35 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3347244 = .branch 193 0 1638546 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode35 p]
theorem oldNode37 (p : Pattern) : eval read p 3347245 = NetHack.Sokoban12CostPartition.d37 p := by
  change eval read p 3347245 = (if p 193 then NetHack.Sokoban12CostPartition.d9 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 3347245 = .branch 193 1638544 1638542 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode9 p]
theorem oldNode38 (p : Pattern) : eval read p 3411928 = NetHack.Sokoban12CostPartition.d38 p := by
  change eval read p 3411928 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d36 p)
  have code : read 3411928 = .branch 192 3347244 3347245 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode36 p, oldNode37 p]
theorem oldNode39 (p : Pattern) : eval read p 3347246 = NetHack.Sokoban12CostPartition.d39 p := by
  change eval read p 3347246 = (if p 193 then NetHack.Sokoban12CostPartition.d16 p else NetHack.Sokoban12CostPartition.d0 p)
  have code : read 3347246 = .branch 193 0 1638544 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode0 p, oldNode16 p]
theorem oldNode40 (p : Pattern) : eval read p 3411929 = NetHack.Sokoban12CostPartition.d40 p := by
  change eval read p 3411929 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d39 p)
  have code : read 3411929 = .branch 192 3347246 3347245 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode39 p, oldNode37 p]
theorem oldNode41 (p : Pattern) : eval read p 3999643 = NetHack.Sokoban12CostPartition.d41 p := by
  change eval read p 3999643 = (if p 168 then NetHack.Sokoban12CostPartition.d40 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 3999643 = .branch 168 3411928 3411929 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode40 p]
theorem oldNode42 (p : Pattern) : eval read p 3411932 = NetHack.Sokoban12CostPartition.d42 p := by
  change eval read p 3411932 = (if p 192 then NetHack.Sokoban12CostPartition.d37 p else NetHack.Sokoban12CostPartition.d16 p)
  have code : read 3411932 = .branch 192 1638544 3347245 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode16 p, oldNode37 p]
theorem oldNode43 (p : Pattern) : eval read p 3999645 = NetHack.Sokoban12CostPartition.d43 p := by
  change eval read p 3999645 = (if p 168 then NetHack.Sokoban12CostPartition.d42 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 3999645 = .branch 168 3411929 3411932 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode42 p]
theorem oldNode54 (p : Pattern) : eval read p 3347233 = NetHack.Sokoban12CostPartition.d54 p := by
  change eval read p 3347233 = (if p 193 then NetHack.Sokoban12CostPartition.d4 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3347233 = .branch 193 2 4 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode4 p]
theorem oldNode55 (p : Pattern) : eval read p 3411913 = NetHack.Sokoban12CostPartition.d55 p := by
  change eval read p 3411913 = (if p 192 then NetHack.Sokoban12CostPartition.d54 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3411913 = .branch 192 2 3347233 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode54 p]
theorem oldNode56 (p : Pattern) : eval read p 3737602 = NetHack.Sokoban12CostPartition.d56 p := by
  change eval read p 3737602 = (if p 186 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3737602 = .branch 186 3411912 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode57 (p : Pattern) : eval read p 4391981 = NetHack.Sokoban12CostPartition.d57 p := by
  change eval read p 4391981 = (if p 160 then NetHack.Sokoban12CostPartition.d56 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 4391981 = .branch 160 3411912 3737602 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode56 p]
theorem oldNode58 (p : Pattern) : eval read p 1638543 = NetHack.Sokoban12CostPartition.d58 p := by
  change eval read p 1638543 = (if p 271 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d4 p)
  have code : read 1638543 = .branch 271 4 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode4 p, oldNode5 p]
theorem oldNode59 (p : Pattern) : eval read p 3347235 = NetHack.Sokoban12CostPartition.d59 p := by
  change eval read p 3347235 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 3347235 = .branch 193 1638542 1638543 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode58 p]
theorem oldNode60 (p : Pattern) : eval read p 3411915 = NetHack.Sokoban12CostPartition.d60 p := by
  change eval read p 3411915 = (if p 192 then NetHack.Sokoban12CostPartition.d59 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 3411915 = .branch 192 1638542 3347235 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode59 p]
theorem oldNode61 (p : Pattern) : eval read p 3737603 = NetHack.Sokoban12CostPartition.d61 p := by
  change eval read p 3737603 = (if p 186 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 3737603 = .branch 186 3411914 3411915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode60 p]
theorem oldNode62 (p : Pattern) : eval read p 3999608 = NetHack.Sokoban12CostPartition.d62 p := by
  change eval read p 3999608 = (if p 168 then NetHack.Sokoban12CostPartition.d61 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 3999608 = .branch 168 3737602 3737603 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode61 p]
end NetHack.Soko12Forward220.Shared
