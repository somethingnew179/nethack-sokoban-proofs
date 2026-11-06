import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode63 (p : Pattern) : eval read p 4391982 = NetHack.Sokoban12CostPartition.d63 p := by
  change eval read p 4391982 = (if p 160 then NetHack.Sokoban12CostPartition.d62 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 4391982 = .branch 160 3999607 3999608 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode62 p]
theorem oldNode64 (p : Pattern) : eval read p 4784968 = NetHack.Sokoban12CostPartition.d64 p := by
  change eval read p 4784968 = (if p 141 then NetHack.Sokoban12CostPartition.d63 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4784968 = .branch 141 4391981 4391982 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode63 p]
theorem oldNode65 (p : Pattern) : eval read p 3999609 = NetHack.Sokoban12CostPartition.d65 p := by
  change eval read p 3999609 = (if p 168 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 3999609 = .branch 168 3411913 3411915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode60 p]
theorem oldNode66 (p : Pattern) : eval read p 4784969 = NetHack.Sokoban12CostPartition.d66 p := by
  change eval read p 4784969 = (if p 141 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 4784969 = .branch 141 3411913 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode65 p]
theorem oldNode67 (p : Pattern) : eval read p 4981385 = NetHack.Sokoban12CostPartition.d67 p := by
  change eval read p 4981385 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 4981385 = .branch 134 4784968 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode66 p]
theorem oldNode68 (p : Pattern) : eval read p 4523360 = NetHack.Sokoban12CostPartition.d68 p := by
  change eval read p 4523360 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4523360 = .branch 158 4391981 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode55 p]
theorem oldNode69 (p : Pattern) : eval read p 4523361 = NetHack.Sokoban12CostPartition.d69 p := by
  change eval read p 4523361 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 4523361 = .branch 158 4391982 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode65 p]
theorem oldNode70 (p : Pattern) : eval read p 4784970 = NetHack.Sokoban12CostPartition.d70 p := by
  change eval read p 4784970 = (if p 141 then NetHack.Sokoban12CostPartition.d69 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 4784970 = .branch 141 4523360 4523361 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode69 p]
theorem oldNode71 (p : Pattern) : eval read p 4981386 = NetHack.Sokoban12CostPartition.d71 p := by
  change eval read p 4981386 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 4981386 = .branch 134 4784970 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode66 p]
theorem oldNode72 (p : Pattern) : eval read p 5046725 = NetHack.Sokoban12CostPartition.d72 p := by
  change eval read p 5046725 = (if p 133 then NetHack.Sokoban12CostPartition.d71 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 5046725 = .branch 133 4981385 4981386 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode71 p]
theorem oldNode73 (p : Pattern) : eval read p 5046726 = NetHack.Sokoban12CostPartition.d73 p := by
  change eval read p 5046726 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d71 p)
  have code : read 5046726 = .branch 133 4981386 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode71 p, oldNode66 p]
theorem oldNode74 (p : Pattern) : eval read p 5112151 = NetHack.Sokoban12CostPartition.d74 p := by
  change eval read p 5112151 = (if p 132 then NetHack.Sokoban12CostPartition.d73 p else NetHack.Sokoban12CostPartition.d72 p)
  have code : read 5112151 = .branch 132 5046725 5046726 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode72 p, oldNode73 p]
theorem oldNode75 (p : Pattern) : eval read p 5439685 = NetHack.Sokoban12CostPartition.d75 p := by
  change eval read p 5439685 = (if p 108 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d74 p)
  have code : read 5439685 = .branch 108 5112151 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode74 p, oldNode66 p]
theorem oldNode106 (p : Pattern) : eval read p 4391983 = NetHack.Sokoban12CostPartition.d106 p := by
  change eval read p 4391983 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 4391983 = .branch 160 3411912 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode107 (p : Pattern) : eval read p 4457751 = NetHack.Sokoban12CostPartition.d107 p := by
  change eval read p 4457751 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4457751 = .branch 159 4391983 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode55 p]
theorem oldNode108 (p : Pattern) : eval read p 4523362 = NetHack.Sokoban12CostPartition.d108 p := by
  change eval read p 4523362 = (if p 158 then NetHack.Sokoban12CostPartition.d107 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4523362 = .branch 158 4391983 4457751 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode107 p]
theorem oldNode109 (p : Pattern) : eval read p 4391984 = NetHack.Sokoban12CostPartition.d109 p := by
  change eval read p 4391984 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 4391984 = .branch 160 3999607 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode65 p]
theorem oldNode110 (p : Pattern) : eval read p 4457752 = NetHack.Sokoban12CostPartition.d110 p := by
  change eval read p 4457752 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 4457752 = .branch 159 4391984 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode65 p]
theorem oldNode111 (p : Pattern) : eval read p 4523363 = NetHack.Sokoban12CostPartition.d111 p := by
  change eval read p 4523363 = (if p 158 then NetHack.Sokoban12CostPartition.d110 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 4523363 = .branch 158 4391984 4457752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode110 p]
theorem oldNode112 (p : Pattern) : eval read p 4784971 = NetHack.Sokoban12CostPartition.d112 p := by
  change eval read p 4784971 = (if p 141 then NetHack.Sokoban12CostPartition.d111 p else NetHack.Sokoban12CostPartition.d108 p)
  have code : read 4784971 = .branch 141 4523362 4523363 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode108 p, oldNode111 p]
theorem oldNode113 (p : Pattern) : eval read p 4981387 = NetHack.Sokoban12CostPartition.d113 p := by
  change eval read p 4981387 = (if p 134 then NetHack.Sokoban12CostPartition.d112 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 4981387 = .branch 134 4784968 4784971 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode112 p]
theorem oldNode114 (p : Pattern) : eval read p 4457753 = NetHack.Sokoban12CostPartition.d114 p := by
  change eval read p 4457753 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4457753 = .branch 159 4391981 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode55 p]
theorem oldNode115 (p : Pattern) : eval read p 4523364 = NetHack.Sokoban12CostPartition.d115 p := by
  change eval read p 4523364 = (if p 158 then NetHack.Sokoban12CostPartition.d114 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4523364 = .branch 158 4391981 4457753 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode114 p]
theorem oldNode116 (p : Pattern) : eval read p 4457754 = NetHack.Sokoban12CostPartition.d116 p := by
  change eval read p 4457754 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 4457754 = .branch 159 4391982 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode65 p]
end NetHack.Soko12Forward220.Shared
