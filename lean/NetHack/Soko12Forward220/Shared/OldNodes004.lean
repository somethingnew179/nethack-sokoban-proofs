import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode141 (p : Pattern) : eval read p 4457760 = NetHack.Sokoban12CostPartition.d141 p := by
  change eval read p 4457760 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d139 p)
  have code : read 4457760 = .branch 159 4391988 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode139 p, oldNode55 p]
theorem oldNode142 (p : Pattern) : eval read p 4523368 = NetHack.Sokoban12CostPartition.d142 p := by
  change eval read p 4523368 = (if p 158 then NetHack.Sokoban12CostPartition.d141 p else NetHack.Sokoban12CostPartition.d140 p)
  have code : read 4523368 = .branch 158 4457759 4457760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode140 p, oldNode141 p]
theorem oldNode143 (p : Pattern) : eval read p 3737607 = NetHack.Sokoban12CostPartition.d143 p := by
  change eval read p 3737607 = (if p 186 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d125 p)
  have code : read 3737607 = .branch 186 3671967 3411915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode125 p, oldNode60 p]
theorem oldNode144 (p : Pattern) : eval read p 3999611 = NetHack.Sokoban12CostPartition.d144 p := by
  change eval read p 3999611 = (if p 168 then NetHack.Sokoban12CostPartition.d143 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 3999611 = .branch 168 3737606 3737607 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode143 p]
theorem oldNode145 (p : Pattern) : eval read p 4391989 = NetHack.Sokoban12CostPartition.d145 p := by
  change eval read p 4391989 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 4391989 = .branch 160 3999607 3999611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode144 p]
theorem oldNode146 (p : Pattern) : eval read p 4391990 = NetHack.Sokoban12CostPartition.d146 p := by
  change eval read p 4391990 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d127 p)
  have code : read 4391990 = .branch 160 3999610 3999611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode127 p, oldNode144 p]
theorem oldNode147 (p : Pattern) : eval read p 4457761 = NetHack.Sokoban12CostPartition.d147 p := by
  change eval read p 4457761 = (if p 159 then NetHack.Sokoban12CostPartition.d146 p else NetHack.Sokoban12CostPartition.d145 p)
  have code : read 4457761 = .branch 159 4391989 4391990 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode145 p, oldNode146 p]
theorem oldNode148 (p : Pattern) : eval read p 4457762 = NetHack.Sokoban12CostPartition.d148 p := by
  change eval read p 4457762 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d146 p)
  have code : read 4457762 = .branch 159 4391990 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode146 p, oldNode65 p]
theorem oldNode149 (p : Pattern) : eval read p 4523369 = NetHack.Sokoban12CostPartition.d149 p := by
  change eval read p 4523369 = (if p 158 then NetHack.Sokoban12CostPartition.d148 p else NetHack.Sokoban12CostPartition.d147 p)
  have code : read 4523369 = .branch 158 4457761 4457762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode147 p, oldNode148 p]
theorem oldNode150 (p : Pattern) : eval read p 4784974 = NetHack.Sokoban12CostPartition.d150 p := by
  change eval read p 4784974 = (if p 141 then NetHack.Sokoban12CostPartition.d149 p else NetHack.Sokoban12CostPartition.d142 p)
  have code : read 4784974 = .branch 141 4523368 4523369 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode142 p, oldNode149 p]
theorem oldNode151 (p : Pattern) : eval read p 4981389 = NetHack.Sokoban12CostPartition.d151 p := by
  change eval read p 4981389 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d150 p)
  have code : read 4981389 = .branch 134 4784974 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode150 p, oldNode66 p]
theorem oldNode152 (p : Pattern) : eval read p 5046729 = NetHack.Sokoban12CostPartition.d152 p := by
  change eval read p 5046729 = (if p 133 then NetHack.Sokoban12CostPartition.d151 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 5046729 = .branch 133 4981385 4981389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode151 p]
theorem oldNode153 (p : Pattern) : eval read p 4457763 = NetHack.Sokoban12CostPartition.d153 p := by
  change eval read p 4457763 = (if p 159 then NetHack.Sokoban12CostPartition.d139 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4457763 = .branch 159 4391981 4391988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode139 p]
theorem oldNode154 (p : Pattern) : eval read p 4523370 = NetHack.Sokoban12CostPartition.d154 p := by
  change eval read p 4523370 = (if p 158 then NetHack.Sokoban12CostPartition.d141 p else NetHack.Sokoban12CostPartition.d153 p)
  have code : read 4523370 = .branch 158 4457763 4457760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode153 p, oldNode141 p]
theorem oldNode155 (p : Pattern) : eval read p 4457764 = NetHack.Sokoban12CostPartition.d155 p := by
  change eval read p 4457764 = (if p 159 then NetHack.Sokoban12CostPartition.d146 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 4457764 = .branch 159 4391982 4391990 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode146 p]
theorem oldNode156 (p : Pattern) : eval read p 4523371 = NetHack.Sokoban12CostPartition.d156 p := by
  change eval read p 4523371 = (if p 158 then NetHack.Sokoban12CostPartition.d148 p else NetHack.Sokoban12CostPartition.d155 p)
  have code : read 4523371 = .branch 158 4457764 4457762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode155 p, oldNode148 p]
theorem oldNode157 (p : Pattern) : eval read p 4784975 = NetHack.Sokoban12CostPartition.d157 p := by
  change eval read p 4784975 = (if p 141 then NetHack.Sokoban12CostPartition.d156 p else NetHack.Sokoban12CostPartition.d154 p)
  have code : read 4784975 = .branch 141 4523370 4523371 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode154 p, oldNode156 p]
theorem oldNode158 (p : Pattern) : eval read p 4981390 = NetHack.Sokoban12CostPartition.d158 p := by
  change eval read p 4981390 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d157 p)
  have code : read 4981390 = .branch 134 4784975 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode157 p, oldNode66 p]
theorem oldNode159 (p : Pattern) : eval read p 5046730 = NetHack.Sokoban12CostPartition.d159 p := by
  change eval read p 5046730 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d158 p)
  have code : read 5046730 = .branch 133 4981390 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode158 p, oldNode66 p]
theorem oldNode160 (p : Pattern) : eval read p 5112153 = NetHack.Sokoban12CostPartition.d160 p := by
  change eval read p 5112153 = (if p 132 then NetHack.Sokoban12CostPartition.d159 p else NetHack.Sokoban12CostPartition.d152 p)
  have code : read 5112153 = .branch 132 5046729 5046730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode152 p, oldNode159 p]
theorem oldNode161 (p : Pattern) : eval read p 5439686 = NetHack.Sokoban12CostPartition.d161 p := by
  change eval read p 5439686 = (if p 108 then NetHack.Sokoban12CostPartition.d160 p else NetHack.Sokoban12CostPartition.d136 p)
  have code : read 5439686 = .branch 108 5112152 5112153 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode136 p, oldNode160 p]
theorem oldNode179 (p : Pattern) : eval read p 4523372 = NetHack.Sokoban12CostPartition.d179 p := by
  change eval read p 4523372 = (if p 158 then NetHack.Sokoban12CostPartition.d122 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4523372 = .branch 158 4391983 4457755 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode122 p]
theorem oldNode180 (p : Pattern) : eval read p 4981391 = NetHack.Sokoban12CostPartition.d180 p := by
  change eval read p 4981391 = (if p 134 then NetHack.Sokoban12CostPartition.d179 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4981391 = .branch 134 4391981 4523372 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode179 p]
theorem oldNode181 (p : Pattern) : eval read p 4523373 = NetHack.Sokoban12CostPartition.d181 p := by
  change eval read p 4523373 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d122 p)
  have code : read 4523373 = .branch 158 4457755 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode122 p, oldNode55 p]
end NetHack.Soko12Forward220.Shared
