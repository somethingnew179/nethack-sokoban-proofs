import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode248 (p : Pattern) : eval read p 368670 = NetHack.Sokoban12CostPartition.d248 p := by
  change eval read p 368670 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d247 p)
  have code : read 368670 = .branch 134 360467 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode247 p, oldNode66 p]
theorem oldNode249 (p : Pattern) : eval read p 335909 = NetHack.Sokoban12CostPartition.d249 p := by
  change eval read p 335909 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d147 p)
  have code : read 335909 = .branch 158 327697 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode147 p, oldNode65 p]
theorem oldNode250 (p : Pattern) : eval read p 360468 = NetHack.Sokoban12CostPartition.d250 p := by
  change eval read p 360468 = (if p 141 then NetHack.Sokoban12CostPartition.d249 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 360468 = .branch 141 335898 335909 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode249 p]
theorem oldNode251 (p : Pattern) : eval read p 368671 = NetHack.Sokoban12CostPartition.d251 p := by
  change eval read p 368671 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d250 p)
  have code : read 368671 = .branch 134 360468 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode250 p, oldNode66 p]
theorem oldNode252 (p : Pattern) : eval read p 376864 = NetHack.Sokoban12CostPartition.d252 p := by
  change eval read p 376864 = (if p 133 then NetHack.Sokoban12CostPartition.d251 p else NetHack.Sokoban12CostPartition.d248 p)
  have code : read 376864 = .branch 133 368670 368671 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode248 p, oldNode251 p]
theorem oldNode253 (p : Pattern) : eval read p 335910 = NetHack.Sokoban12CostPartition.d253 p := by
  change eval read p 335910 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d155 p)
  have code : read 335910 = .branch 158 327700 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode155 p, oldNode65 p]
theorem oldNode254 (p : Pattern) : eval read p 360469 = NetHack.Sokoban12CostPartition.d254 p := by
  change eval read p 360469 = (if p 141 then NetHack.Sokoban12CostPartition.d253 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 360469 = .branch 141 335899 335910 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode253 p]
theorem oldNode255 (p : Pattern) : eval read p 368672 = NetHack.Sokoban12CostPartition.d255 p := by
  change eval read p 368672 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d254 p)
  have code : read 368672 = .branch 134 360469 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode254 p, oldNode66 p]
theorem oldNode256 (p : Pattern) : eval read p 376865 = NetHack.Sokoban12CostPartition.d256 p := by
  change eval read p 376865 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d255 p)
  have code : read 376865 = .branch 133 368672 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode255 p, oldNode66 p]
theorem oldNode257 (p : Pattern) : eval read p 385045 = NetHack.Sokoban12CostPartition.d257 p := by
  change eval read p 385045 = (if p 132 then NetHack.Sokoban12CostPartition.d256 p else NetHack.Sokoban12CostPartition.d252 p)
  have code : read 385045 = .branch 132 376864 376865 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode252 p, oldNode256 p]
theorem oldNode258 (p : Pattern) : eval read p 409612 = NetHack.Sokoban12CostPartition.d258 p := by
  change eval read p 409612 = (if p 108 then NetHack.Sokoban12CostPartition.d257 p else NetHack.Sokoban12CostPartition.d245 p)
  have code : read 409612 = .branch 108 385044 385045 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode245 p, oldNode257 p]
theorem oldNode259 (p : Pattern) : eval read p 221195 = NetHack.Sokoban12CostPartition.d259 p := by
  change eval read p 221195 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 221195 = .branch 193 2 90116 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode58 p]
theorem oldNode260 (p : Pattern) : eval read p 229389 = NetHack.Sokoban12CostPartition.d260 p := by
  change eval read p 229389 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d259 p)
  have code : read 229389 = .branch 192 221195 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode259 p, oldNode5 p]
theorem oldNode261 (p : Pattern) : eval read p 270345 = NetHack.Sokoban12CostPartition.d261 p := by
  change eval read p 270345 = (if p 186 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 270345 = .branch 186 229378 229389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode260 p]
theorem oldNode262 (p : Pattern) : eval read p 90117 = NetHack.Sokoban12CostPartition.d262 p := by
  change eval read p 90117 = (if p 271 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 90117 = .branch 271 2 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode263 (p : Pattern) : eval read p 221196 = NetHack.Sokoban12CostPartition.d263 p := by
  change eval read p 221196 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 221196 = .branch 193 90117 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode5 p]
theorem oldNode264 (p : Pattern) : eval read p 229390 = NetHack.Sokoban12CostPartition.d264 p := by
  change eval read p 229390 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d263 p)
  have code : read 229390 = .branch 192 221196 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode263 p, oldNode5 p]
theorem oldNode265 (p : Pattern) : eval read p 270346 = NetHack.Sokoban12CostPartition.d265 p := by
  change eval read p 270346 = (if p 186 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 270346 = .branch 186 229379 229390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode264 p]
theorem oldNode266 (p : Pattern) : eval read p 286733 = NetHack.Sokoban12CostPartition.d266 p := by
  change eval read p 286733 = (if p 168 then NetHack.Sokoban12CostPartition.d265 p else NetHack.Sokoban12CostPartition.d261 p)
  have code : read 286733 = .branch 168 270345 270346 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode261 p, oldNode265 p]
theorem oldNode267 (p : Pattern) : eval read p 319503 = NetHack.Sokoban12CostPartition.d267 p := by
  change eval read p 319503 = (if p 160 then NetHack.Sokoban12CostPartition.d266 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 319503 = .branch 160 286721 286733 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode266 p]
theorem oldNode268 (p : Pattern) : eval read p 360470 = NetHack.Sokoban12CostPartition.d268 p := by
  change eval read p 360470 = (if p 141 then NetHack.Sokoban12CostPartition.d267 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 360470 = .branch 141 319489 319503 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode267 p]
theorem oldNode269 (p : Pattern) : eval read p 286734 = NetHack.Sokoban12CostPartition.d269 p := by
  change eval read p 286734 = (if p 168 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d260 p)
  have code : read 286734 = .branch 168 229389 229390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode260 p, oldNode264 p]
theorem oldNode270 (p : Pattern) : eval read p 319504 = NetHack.Sokoban12CostPartition.d270 p := by
  change eval read p 319504 = (if p 160 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 319504 = .branch 160 286721 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode269 p]
theorem oldNode271 (p : Pattern) : eval read p 262147 = NetHack.Sokoban12CostPartition.d271 p := by
  change eval read p 262147 = (if p 187 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 262147 = .branch 187 229378 229389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode260 p]
end NetHack.Soko12Forward219.Shared
