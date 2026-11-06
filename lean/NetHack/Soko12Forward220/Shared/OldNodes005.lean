import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode182 (p : Pattern) : eval read p 4981392 = NetHack.Sokoban12CostPartition.d182 p := by
  change eval read p 4981392 = (if p 134 then NetHack.Sokoban12CostPartition.d181 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 4981392 = .branch 134 4523360 4523373 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode181 p]
theorem oldNode183 (p : Pattern) : eval read p 5046731 = NetHack.Sokoban12CostPartition.d183 p := by
  change eval read p 5046731 = (if p 133 then NetHack.Sokoban12CostPartition.d182 p else NetHack.Sokoban12CostPartition.d180 p)
  have code : read 5046731 = .branch 133 4981391 4981392 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode180 p, oldNode182 p]
theorem oldNode184 (p : Pattern) : eval read p 5046732 = NetHack.Sokoban12CostPartition.d184 p := by
  change eval read p 5046732 = (if p 133 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d182 p)
  have code : read 5046732 = .branch 133 4981392 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode182 p, oldNode55 p]
theorem oldNode185 (p : Pattern) : eval read p 5112154 = NetHack.Sokoban12CostPartition.d185 p := by
  change eval read p 5112154 = (if p 132 then NetHack.Sokoban12CostPartition.d184 p else NetHack.Sokoban12CostPartition.d183 p)
  have code : read 5112154 = .branch 132 5046731 5046732 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode183 p, oldNode184 p]
theorem oldNode186 (p : Pattern) : eval read p 4523374 = NetHack.Sokoban12CostPartition.d186 p := by
  change eval read p 4523374 = (if p 158 then NetHack.Sokoban12CostPartition.d153 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4523374 = .branch 158 4391981 4457763 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode153 p]
theorem oldNode187 (p : Pattern) : eval read p 4981393 = NetHack.Sokoban12CostPartition.d187 p := by
  change eval read p 4981393 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 4981393 = .branch 134 4523374 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode55 p]
theorem oldNode188 (p : Pattern) : eval read p 4523375 = NetHack.Sokoban12CostPartition.d188 p := by
  change eval read p 4523375 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d140 p)
  have code : read 4523375 = .branch 158 4457759 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode140 p, oldNode55 p]
theorem oldNode189 (p : Pattern) : eval read p 4981394 = NetHack.Sokoban12CostPartition.d189 p := by
  change eval read p 4981394 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 4981394 = .branch 134 4523375 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode55 p]
theorem oldNode190 (p : Pattern) : eval read p 5046733 = NetHack.Sokoban12CostPartition.d190 p := by
  change eval read p 5046733 = (if p 133 then NetHack.Sokoban12CostPartition.d189 p else NetHack.Sokoban12CostPartition.d187 p)
  have code : read 5046733 = .branch 133 4981393 4981394 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode187 p, oldNode189 p]
theorem oldNode191 (p : Pattern) : eval read p 4523376 = NetHack.Sokoban12CostPartition.d191 p := by
  change eval read p 4523376 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d153 p)
  have code : read 4523376 = .branch 158 4457763 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode153 p, oldNode55 p]
theorem oldNode192 (p : Pattern) : eval read p 4981395 = NetHack.Sokoban12CostPartition.d192 p := by
  change eval read p 4981395 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 4981395 = .branch 134 4523376 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode55 p]
theorem oldNode193 (p : Pattern) : eval read p 5046734 = NetHack.Sokoban12CostPartition.d193 p := by
  change eval read p 5046734 = (if p 133 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d192 p)
  have code : read 5046734 = .branch 133 4981395 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode192 p, oldNode55 p]
theorem oldNode194 (p : Pattern) : eval read p 5112155 = NetHack.Sokoban12CostPartition.d194 p := by
  change eval read p 5112155 = (if p 132 then NetHack.Sokoban12CostPartition.d193 p else NetHack.Sokoban12CostPartition.d190 p)
  have code : read 5112155 = .branch 132 5046733 5046734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode190 p, oldNode193 p]
theorem oldNode195 (p : Pattern) : eval read p 5439687 = NetHack.Sokoban12CostPartition.d195 p := by
  change eval read p 5439687 = (if p 108 then NetHack.Sokoban12CostPartition.d194 p else NetHack.Sokoban12CostPartition.d185 p)
  have code : read 5439687 = .branch 108 5112154 5112155 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode185 p, oldNode194 p]
theorem oldNode199 (p : Pattern) : eval read p 5112156 = NetHack.Sokoban12CostPartition.d199 p := by
  change eval read p 5112156 = (if p 132 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d134 p)
  have code : read 5112156 = .branch 132 5046727 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode134 p, oldNode66 p]
theorem oldNode200 (p : Pattern) : eval read p 5112157 = NetHack.Sokoban12CostPartition.d200 p := by
  change eval read p 5112157 = (if p 132 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d152 p)
  have code : read 5112157 = .branch 132 5046729 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode152 p, oldNode66 p]
theorem oldNode201 (p : Pattern) : eval read p 5439688 = NetHack.Sokoban12CostPartition.d201 p := by
  change eval read p 5439688 = (if p 108 then NetHack.Sokoban12CostPartition.d200 p else NetHack.Sokoban12CostPartition.d199 p)
  have code : read 5439688 = .branch 108 5112156 5112157 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode199 p, oldNode200 p]
theorem oldNode210 (p : Pattern) : eval read p 5046735 = NetHack.Sokoban12CostPartition.d210 p := by
  change eval read p 5046735 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d113 p)
  have code : read 5046735 = .branch 133 4981387 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode113 p, oldNode66 p]
theorem oldNode211 (p : Pattern) : eval read p 4523377 = NetHack.Sokoban12CostPartition.d211 p := by
  change eval read p 4523377 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d107 p)
  have code : read 4523377 = .branch 158 4457751 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode107 p, oldNode55 p]
theorem oldNode212 (p : Pattern) : eval read p 4523378 = NetHack.Sokoban12CostPartition.d212 p := by
  change eval read p 4523378 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d110 p)
  have code : read 4523378 = .branch 158 4457752 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode110 p, oldNode65 p]
theorem oldNode213 (p : Pattern) : eval read p 4784976 = NetHack.Sokoban12CostPartition.d213 p := by
  change eval read p 4784976 = (if p 141 then NetHack.Sokoban12CostPartition.d212 p else NetHack.Sokoban12CostPartition.d211 p)
  have code : read 4784976 = .branch 141 4523377 4523378 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode211 p, oldNode212 p]
theorem oldNode214 (p : Pattern) : eval read p 4981396 = NetHack.Sokoban12CostPartition.d214 p := by
  change eval read p 4981396 = (if p 134 then NetHack.Sokoban12CostPartition.d213 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 4981396 = .branch 134 4784970 4784976 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode213 p]
theorem oldNode215 (p : Pattern) : eval read p 5046736 = NetHack.Sokoban12CostPartition.d215 p := by
  change eval read p 5046736 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d214 p)
  have code : read 5046736 = .branch 133 4981396 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode214 p, oldNode66 p]
theorem oldNode216 (p : Pattern) : eval read p 5112158 = NetHack.Sokoban12CostPartition.d216 p := by
  change eval read p 5112158 = (if p 132 then NetHack.Sokoban12CostPartition.d215 p else NetHack.Sokoban12CostPartition.d210 p)
  have code : read 5112158 = .branch 132 5046735 5046736 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode210 p, oldNode215 p]
end NetHack.Soko12Forward220.Shared
