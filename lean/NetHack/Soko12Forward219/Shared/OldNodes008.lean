import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode272 (p : Pattern) : eval read p 270347 = NetHack.Sokoban12CostPartition.d272 p := by
  change eval read p 270347 = (if p 186 then NetHack.Sokoban12CostPartition.d271 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 270347 = .branch 186 229378 262147 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode271 p]
theorem oldNode273 (p : Pattern) : eval read p 262148 = NetHack.Sokoban12CostPartition.d273 p := by
  change eval read p 262148 = (if p 187 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 262148 = .branch 187 229379 229390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode264 p]
theorem oldNode274 (p : Pattern) : eval read p 270348 = NetHack.Sokoban12CostPartition.d274 p := by
  change eval read p 270348 = (if p 186 then NetHack.Sokoban12CostPartition.d273 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 270348 = .branch 186 229379 262148 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode273 p]
theorem oldNode275 (p : Pattern) : eval read p 286735 = NetHack.Sokoban12CostPartition.d275 p := by
  change eval read p 286735 = (if p 168 then NetHack.Sokoban12CostPartition.d274 p else NetHack.Sokoban12CostPartition.d272 p)
  have code : read 286735 = .branch 168 270347 270348 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode272 p, oldNode274 p]
theorem oldNode276 (p : Pattern) : eval read p 319505 = NetHack.Sokoban12CostPartition.d276 p := by
  change eval read p 319505 = (if p 160 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d275 p)
  have code : read 319505 = .branch 160 286735 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode275 p, oldNode269 p]
theorem oldNode277 (p : Pattern) : eval read p 327701 = NetHack.Sokoban12CostPartition.d277 p := by
  change eval read p 327701 = (if p 159 then NetHack.Sokoban12CostPartition.d276 p else NetHack.Sokoban12CostPartition.d270 p)
  have code : read 327701 = .branch 159 319504 319505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode270 p, oldNode276 p]
theorem oldNode278 (p : Pattern) : eval read p 335911 = NetHack.Sokoban12CostPartition.d278 p := by
  change eval read p 335911 = (if p 158 then NetHack.Sokoban12CostPartition.d277 p else NetHack.Sokoban12CostPartition.d270 p)
  have code : read 335911 = .branch 158 319504 327701 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode270 p, oldNode277 p]
theorem oldNode279 (p : Pattern) : eval read p 360471 = NetHack.Sokoban12CostPartition.d279 p := by
  change eval read p 360471 = (if p 141 then NetHack.Sokoban12CostPartition.d278 p else NetHack.Sokoban12CostPartition.d179 p)
  have code : read 360471 = .branch 141 335895 335911 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode179 p, oldNode278 p]
theorem oldNode280 (p : Pattern) : eval read p 368673 = NetHack.Sokoban12CostPartition.d280 p := by
  change eval read p 368673 = (if p 134 then NetHack.Sokoban12CostPartition.d279 p else NetHack.Sokoban12CostPartition.d268 p)
  have code : read 368673 = .branch 134 360470 360471 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode268 p, oldNode279 p]
theorem oldNode281 (p : Pattern) : eval read p 335912 = NetHack.Sokoban12CostPartition.d281 p := by
  change eval read p 335912 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 335912 = .branch 158 319503 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode269 p]
theorem oldNode282 (p : Pattern) : eval read p 360472 = NetHack.Sokoban12CostPartition.d282 p := by
  change eval read p 360472 = (if p 141 then NetHack.Sokoban12CostPartition.d281 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 360472 = .branch 141 335873 335912 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode281 p]
theorem oldNode283 (p : Pattern) : eval read p 335913 = NetHack.Sokoban12CostPartition.d283 p := by
  change eval read p 335913 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d277 p)
  have code : read 335913 = .branch 158 327701 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode277 p, oldNode269 p]
theorem oldNode284 (p : Pattern) : eval read p 360473 = NetHack.Sokoban12CostPartition.d284 p := by
  change eval read p 360473 = (if p 141 then NetHack.Sokoban12CostPartition.d283 p else NetHack.Sokoban12CostPartition.d181 p)
  have code : read 360473 = .branch 141 335896 335913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode181 p, oldNode283 p]
theorem oldNode285 (p : Pattern) : eval read p 368674 = NetHack.Sokoban12CostPartition.d285 p := by
  change eval read p 368674 = (if p 134 then NetHack.Sokoban12CostPartition.d284 p else NetHack.Sokoban12CostPartition.d282 p)
  have code : read 368674 = .branch 134 360472 360473 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode282 p, oldNode284 p]
theorem oldNode286 (p : Pattern) : eval read p 376866 = NetHack.Sokoban12CostPartition.d286 p := by
  change eval read p 376866 = (if p 133 then NetHack.Sokoban12CostPartition.d285 p else NetHack.Sokoban12CostPartition.d280 p)
  have code : read 376866 = .branch 133 368673 368674 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode280 p, oldNode285 p]
theorem oldNode287 (p : Pattern) : eval read p 360474 = NetHack.Sokoban12CostPartition.d287 p := by
  change eval read p 360474 = (if p 141 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 360474 = .branch 141 229387 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode269 p]
theorem oldNode288 (p : Pattern) : eval read p 376867 = NetHack.Sokoban12CostPartition.d288 p := by
  change eval read p 376867 = (if p 133 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d285 p)
  have code : read 376867 = .branch 133 368674 360474 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode285 p, oldNode287 p]
theorem oldNode289 (p : Pattern) : eval read p 385046 = NetHack.Sokoban12CostPartition.d289 p := by
  change eval read p 385046 = (if p 132 then NetHack.Sokoban12CostPartition.d288 p else NetHack.Sokoban12CostPartition.d286 p)
  have code : read 385046 = .branch 132 376866 376867 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode286 p, oldNode288 p]
theorem oldNode290 (p : Pattern) : eval read p 270349 = NetHack.Sokoban12CostPartition.d290 p := by
  change eval read p 270349 = (if p 186 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d271 p)
  have code : read 270349 = .branch 186 262147 229389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode271 p, oldNode260 p]
theorem oldNode291 (p : Pattern) : eval read p 270350 = NetHack.Sokoban12CostPartition.d291 p := by
  change eval read p 270350 = (if p 186 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d273 p)
  have code : read 270350 = .branch 186 262148 229390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode273 p, oldNode264 p]
theorem oldNode292 (p : Pattern) : eval read p 286736 = NetHack.Sokoban12CostPartition.d292 p := by
  change eval read p 286736 = (if p 168 then NetHack.Sokoban12CostPartition.d291 p else NetHack.Sokoban12CostPartition.d290 p)
  have code : read 286736 = .branch 168 270349 270350 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode290 p, oldNode291 p]
theorem oldNode293 (p : Pattern) : eval read p 319506 = NetHack.Sokoban12CostPartition.d293 p := by
  change eval read p 319506 = (if p 160 then NetHack.Sokoban12CostPartition.d292 p else NetHack.Sokoban12CostPartition.d275 p)
  have code : read 319506 = .branch 160 286735 286736 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode275 p, oldNode292 p]
theorem oldNode294 (p : Pattern) : eval read p 327702 = NetHack.Sokoban12CostPartition.d294 p := by
  change eval read p 327702 = (if p 159 then NetHack.Sokoban12CostPartition.d293 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 327702 = .branch 159 319503 319506 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode293 p]
theorem oldNode295 (p : Pattern) : eval read p 335914 = NetHack.Sokoban12CostPartition.d295 p := by
  change eval read p 335914 = (if p 158 then NetHack.Sokoban12CostPartition.d294 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 335914 = .branch 158 319503 327702 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode294 p]
end NetHack.Soko12Forward219.Shared
