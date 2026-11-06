import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode248 (p : Pattern) : eval read p 4981401 = NetHack.Sokoban12CostPartition.d248 p := by
  change eval read p 4981401 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d247 p)
  have code : read 4981401 = .branch 134 4784981 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode247 p, oldNode66 p]
theorem oldNode249 (p : Pattern) : eval read p 4523384 = NetHack.Sokoban12CostPartition.d249 p := by
  change eval read p 4523384 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d147 p)
  have code : read 4523384 = .branch 158 4457761 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode147 p, oldNode65 p]
theorem oldNode250 (p : Pattern) : eval read p 4784982 = NetHack.Sokoban12CostPartition.d250 p := by
  change eval read p 4784982 = (if p 141 then NetHack.Sokoban12CostPartition.d249 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 4784982 = .branch 141 4523375 4523384 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode249 p]
theorem oldNode251 (p : Pattern) : eval read p 4981402 = NetHack.Sokoban12CostPartition.d251 p := by
  change eval read p 4981402 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d250 p)
  have code : read 4981402 = .branch 134 4784982 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode250 p, oldNode66 p]
theorem oldNode252 (p : Pattern) : eval read p 5046742 = NetHack.Sokoban12CostPartition.d252 p := by
  change eval read p 5046742 = (if p 133 then NetHack.Sokoban12CostPartition.d251 p else NetHack.Sokoban12CostPartition.d248 p)
  have code : read 5046742 = .branch 133 4981401 4981402 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode248 p, oldNode251 p]
theorem oldNode253 (p : Pattern) : eval read p 4523385 = NetHack.Sokoban12CostPartition.d253 p := by
  change eval read p 4523385 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d155 p)
  have code : read 4523385 = .branch 158 4457764 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode155 p, oldNode65 p]
theorem oldNode254 (p : Pattern) : eval read p 4784983 = NetHack.Sokoban12CostPartition.d254 p := by
  change eval read p 4784983 = (if p 141 then NetHack.Sokoban12CostPartition.d253 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 4784983 = .branch 141 4523376 4523385 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode253 p]
theorem oldNode255 (p : Pattern) : eval read p 4981403 = NetHack.Sokoban12CostPartition.d255 p := by
  change eval read p 4981403 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d254 p)
  have code : read 4981403 = .branch 134 4784983 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode254 p, oldNode66 p]
theorem oldNode256 (p : Pattern) : eval read p 5046743 = NetHack.Sokoban12CostPartition.d256 p := by
  change eval read p 5046743 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d255 p)
  have code : read 5046743 = .branch 133 4981403 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode255 p, oldNode66 p]
theorem oldNode257 (p : Pattern) : eval read p 5112162 = NetHack.Sokoban12CostPartition.d257 p := by
  change eval read p 5112162 = (if p 132 then NetHack.Sokoban12CostPartition.d256 p else NetHack.Sokoban12CostPartition.d252 p)
  have code : read 5112162 = .branch 132 5046742 5046743 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode252 p, oldNode256 p]
theorem oldNode258 (p : Pattern) : eval read p 5439691 = NetHack.Sokoban12CostPartition.d258 p := by
  change eval read p 5439691 = (if p 108 then NetHack.Sokoban12CostPartition.d257 p else NetHack.Sokoban12CostPartition.d245 p)
  have code : read 5439691 = .branch 108 5112161 5112162 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode245 p, oldNode257 p]
theorem oldNode259 (p : Pattern) : eval read p 3347238 = NetHack.Sokoban12CostPartition.d259 p := by
  change eval read p 3347238 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3347238 = .branch 193 2 1638543 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode58 p]
theorem oldNode260 (p : Pattern) : eval read p 3411918 = NetHack.Sokoban12CostPartition.d260 p := by
  change eval read p 3411918 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d259 p)
  have code : read 3411918 = .branch 192 3347238 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode259 p, oldNode5 p]
theorem oldNode261 (p : Pattern) : eval read p 3737608 = NetHack.Sokoban12CostPartition.d261 p := by
  change eval read p 3737608 = (if p 186 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 3737608 = .branch 186 3411916 3411918 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode260 p]
theorem oldNode262 (p : Pattern) : eval read p 1638545 = NetHack.Sokoban12CostPartition.d262 p := by
  change eval read p 1638545 = (if p 271 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 1638545 = .branch 271 2 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode263 (p : Pattern) : eval read p 3347239 = NetHack.Sokoban12CostPartition.d263 p := by
  change eval read p 3347239 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 3347239 = .branch 193 1638545 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode5 p]
theorem oldNode264 (p : Pattern) : eval read p 3411919 = NetHack.Sokoban12CostPartition.d264 p := by
  change eval read p 3411919 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d263 p)
  have code : read 3411919 = .branch 192 3347239 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode263 p, oldNode5 p]
theorem oldNode265 (p : Pattern) : eval read p 3737609 = NetHack.Sokoban12CostPartition.d265 p := by
  change eval read p 3737609 = (if p 186 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 3737609 = .branch 186 3411917 3411919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode264 p]
theorem oldNode266 (p : Pattern) : eval read p 3999613 = NetHack.Sokoban12CostPartition.d266 p := by
  change eval read p 3999613 = (if p 168 then NetHack.Sokoban12CostPartition.d265 p else NetHack.Sokoban12CostPartition.d261 p)
  have code : read 3999613 = .branch 168 3737608 3737609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode261 p, oldNode265 p]
theorem oldNode267 (p : Pattern) : eval read p 4391991 = NetHack.Sokoban12CostPartition.d267 p := by
  change eval read p 4391991 = (if p 160 then NetHack.Sokoban12CostPartition.d266 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 4391991 = .branch 160 3999612 3999613 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode266 p]
theorem oldNode268 (p : Pattern) : eval read p 4784984 = NetHack.Sokoban12CostPartition.d268 p := by
  change eval read p 4784984 = (if p 141 then NetHack.Sokoban12CostPartition.d267 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 4784984 = .branch 141 4391981 4391991 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode267 p]
theorem oldNode269 (p : Pattern) : eval read p 3999614 = NetHack.Sokoban12CostPartition.d269 p := by
  change eval read p 3999614 = (if p 168 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d260 p)
  have code : read 3999614 = .branch 168 3411918 3411919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode260 p, oldNode264 p]
theorem oldNode270 (p : Pattern) : eval read p 4391992 = NetHack.Sokoban12CostPartition.d270 p := by
  change eval read p 4391992 = (if p 160 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 4391992 = .branch 160 3999612 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode269 p]
theorem oldNode271 (p : Pattern) : eval read p 3671968 = NetHack.Sokoban12CostPartition.d271 p := by
  change eval read p 3671968 = (if p 187 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 3671968 = .branch 187 3411916 3411918 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode260 p]
end NetHack.Soko12Forward220.Shared
