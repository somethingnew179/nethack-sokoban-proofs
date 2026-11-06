import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode117 (p : Pattern) : eval read p 4523365 = NetHack.Sokoban12CostPartition.d117 p := by
  change eval read p 4523365 = (if p 158 then NetHack.Sokoban12CostPartition.d116 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 4523365 = .branch 158 4391982 4457754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode116 p]
theorem oldNode118 (p : Pattern) : eval read p 4784972 = NetHack.Sokoban12CostPartition.d118 p := by
  change eval read p 4784972 = (if p 141 then NetHack.Sokoban12CostPartition.d117 p else NetHack.Sokoban12CostPartition.d115 p)
  have code : read 4784972 = .branch 141 4523364 4523365 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode115 p, oldNode117 p]
theorem oldNode119 (p : Pattern) : eval read p 3671966 = NetHack.Sokoban12CostPartition.d119 p := by
  change eval read p 3671966 = (if p 187 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3671966 = .branch 187 3411912 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode120 (p : Pattern) : eval read p 3737604 = NetHack.Sokoban12CostPartition.d120 p := by
  change eval read p 3737604 = (if p 186 then NetHack.Sokoban12CostPartition.d119 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 3737604 = .branch 186 3411912 3671966 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode119 p]
theorem oldNode121 (p : Pattern) : eval read p 4391985 = NetHack.Sokoban12CostPartition.d121 p := by
  change eval read p 4391985 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 4391985 = .branch 160 3737604 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode55 p]
theorem oldNode122 (p : Pattern) : eval read p 4457755 = NetHack.Sokoban12CostPartition.d122 p := by
  change eval read p 4457755 = (if p 159 then NetHack.Sokoban12CostPartition.d121 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4457755 = .branch 159 4391983 4391985 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode121 p]
theorem oldNode123 (p : Pattern) : eval read p 4457756 = NetHack.Sokoban12CostPartition.d123 p := by
  change eval read p 4457756 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d121 p)
  have code : read 4457756 = .branch 159 4391985 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode121 p, oldNode55 p]
theorem oldNode124 (p : Pattern) : eval read p 4523366 = NetHack.Sokoban12CostPartition.d124 p := by
  change eval read p 4523366 = (if p 158 then NetHack.Sokoban12CostPartition.d123 p else NetHack.Sokoban12CostPartition.d122 p)
  have code : read 4523366 = .branch 158 4457755 4457756 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode122 p, oldNode123 p]
theorem oldNode125 (p : Pattern) : eval read p 3671967 = NetHack.Sokoban12CostPartition.d125 p := by
  change eval read p 3671967 = (if p 187 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 3671967 = .branch 187 3411914 3411915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode60 p]
theorem oldNode126 (p : Pattern) : eval read p 3737605 = NetHack.Sokoban12CostPartition.d126 p := by
  change eval read p 3737605 = (if p 186 then NetHack.Sokoban12CostPartition.d125 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 3737605 = .branch 186 3411914 3671967 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode125 p]
theorem oldNode127 (p : Pattern) : eval read p 3999610 = NetHack.Sokoban12CostPartition.d127 p := by
  change eval read p 3999610 = (if p 168 then NetHack.Sokoban12CostPartition.d126 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 3999610 = .branch 168 3737604 3737605 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode126 p]
theorem oldNode128 (p : Pattern) : eval read p 4391986 = NetHack.Sokoban12CostPartition.d128 p := by
  change eval read p 4391986 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d127 p)
  have code : read 4391986 = .branch 160 3999610 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode127 p, oldNode65 p]
theorem oldNode129 (p : Pattern) : eval read p 4457757 = NetHack.Sokoban12CostPartition.d129 p := by
  change eval read p 4457757 = (if p 159 then NetHack.Sokoban12CostPartition.d128 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 4457757 = .branch 159 4391984 4391986 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode128 p]
theorem oldNode130 (p : Pattern) : eval read p 4457758 = NetHack.Sokoban12CostPartition.d130 p := by
  change eval read p 4457758 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d128 p)
  have code : read 4457758 = .branch 159 4391986 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode128 p, oldNode65 p]
theorem oldNode131 (p : Pattern) : eval read p 4523367 = NetHack.Sokoban12CostPartition.d131 p := by
  change eval read p 4523367 = (if p 158 then NetHack.Sokoban12CostPartition.d130 p else NetHack.Sokoban12CostPartition.d129 p)
  have code : read 4523367 = .branch 158 4457757 4457758 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode129 p, oldNode130 p]
theorem oldNode132 (p : Pattern) : eval read p 4784973 = NetHack.Sokoban12CostPartition.d132 p := by
  change eval read p 4784973 = (if p 141 then NetHack.Sokoban12CostPartition.d131 p else NetHack.Sokoban12CostPartition.d124 p)
  have code : read 4784973 = .branch 141 4523366 4523367 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode124 p, oldNode131 p]
theorem oldNode133 (p : Pattern) : eval read p 4981388 = NetHack.Sokoban12CostPartition.d133 p := by
  change eval read p 4981388 = (if p 134 then NetHack.Sokoban12CostPartition.d132 p else NetHack.Sokoban12CostPartition.d118 p)
  have code : read 4981388 = .branch 134 4784972 4784973 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode118 p, oldNode132 p]
theorem oldNode134 (p : Pattern) : eval read p 5046727 = NetHack.Sokoban12CostPartition.d134 p := by
  change eval read p 5046727 = (if p 133 then NetHack.Sokoban12CostPartition.d133 p else NetHack.Sokoban12CostPartition.d113 p)
  have code : read 5046727 = .branch 133 4981387 4981388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode113 p, oldNode133 p]
theorem oldNode135 (p : Pattern) : eval read p 5046728 = NetHack.Sokoban12CostPartition.d135 p := by
  change eval read p 5046728 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d133 p)
  have code : read 5046728 = .branch 133 4981388 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode133 p, oldNode66 p]
theorem oldNode136 (p : Pattern) : eval read p 5112152 = NetHack.Sokoban12CostPartition.d136 p := by
  change eval read p 5112152 = (if p 132 then NetHack.Sokoban12CostPartition.d135 p else NetHack.Sokoban12CostPartition.d134 p)
  have code : read 5112152 = .branch 132 5046727 5046728 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode134 p, oldNode135 p]
theorem oldNode137 (p : Pattern) : eval read p 3737606 = NetHack.Sokoban12CostPartition.d137 p := by
  change eval read p 3737606 = (if p 186 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 3737606 = .branch 186 3671966 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode55 p]
theorem oldNode138 (p : Pattern) : eval read p 4391987 = NetHack.Sokoban12CostPartition.d138 p := by
  change eval read p 4391987 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 4391987 = .branch 160 3411912 3737606 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode137 p]
theorem oldNode139 (p : Pattern) : eval read p 4391988 = NetHack.Sokoban12CostPartition.d139 p := by
  change eval read p 4391988 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 4391988 = .branch 160 3737604 3737606 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode137 p]
theorem oldNode140 (p : Pattern) : eval read p 4457759 = NetHack.Sokoban12CostPartition.d140 p := by
  change eval read p 4457759 = (if p 159 then NetHack.Sokoban12CostPartition.d139 p else NetHack.Sokoban12CostPartition.d138 p)
  have code : read 4457759 = .branch 159 4391987 4391988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode138 p, oldNode139 p]
end NetHack.Soko12Forward220.Shared
