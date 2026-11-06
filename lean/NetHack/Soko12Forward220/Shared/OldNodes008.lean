import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode272 (p : Pattern) : eval read p 3737610 = NetHack.Sokoban12CostPartition.d272 p := by
  change eval read p 3737610 = (if p 186 then NetHack.Sokoban12CostPartition.d271 p else NetHack.Sokoban12CostPartition.d15 p)
  have code : read 3737610 = .branch 186 3411916 3671968 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode15 p, oldNode271 p]
theorem oldNode273 (p : Pattern) : eval read p 3671969 = NetHack.Sokoban12CostPartition.d273 p := by
  change eval read p 3671969 = (if p 187 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 3671969 = .branch 187 3411917 3411919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode264 p]
theorem oldNode274 (p : Pattern) : eval read p 3737611 = NetHack.Sokoban12CostPartition.d274 p := by
  change eval read p 3737611 = (if p 186 then NetHack.Sokoban12CostPartition.d273 p else NetHack.Sokoban12CostPartition.d18 p)
  have code : read 3737611 = .branch 186 3411917 3671969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode18 p, oldNode273 p]
theorem oldNode275 (p : Pattern) : eval read p 3999615 = NetHack.Sokoban12CostPartition.d275 p := by
  change eval read p 3999615 = (if p 168 then NetHack.Sokoban12CostPartition.d274 p else NetHack.Sokoban12CostPartition.d272 p)
  have code : read 3999615 = .branch 168 3737610 3737611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode272 p, oldNode274 p]
theorem oldNode276 (p : Pattern) : eval read p 4391993 = NetHack.Sokoban12CostPartition.d276 p := by
  change eval read p 4391993 = (if p 160 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d275 p)
  have code : read 4391993 = .branch 160 3999615 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode275 p, oldNode269 p]
theorem oldNode277 (p : Pattern) : eval read p 4457765 = NetHack.Sokoban12CostPartition.d277 p := by
  change eval read p 4457765 = (if p 159 then NetHack.Sokoban12CostPartition.d276 p else NetHack.Sokoban12CostPartition.d270 p)
  have code : read 4457765 = .branch 159 4391992 4391993 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode270 p, oldNode276 p]
theorem oldNode278 (p : Pattern) : eval read p 4523386 = NetHack.Sokoban12CostPartition.d278 p := by
  change eval read p 4523386 = (if p 158 then NetHack.Sokoban12CostPartition.d277 p else NetHack.Sokoban12CostPartition.d270 p)
  have code : read 4523386 = .branch 158 4391992 4457765 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode270 p, oldNode277 p]
theorem oldNode279 (p : Pattern) : eval read p 4784985 = NetHack.Sokoban12CostPartition.d279 p := by
  change eval read p 4784985 = (if p 141 then NetHack.Sokoban12CostPartition.d278 p else NetHack.Sokoban12CostPartition.d179 p)
  have code : read 4784985 = .branch 141 4523372 4523386 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode179 p, oldNode278 p]
theorem oldNode280 (p : Pattern) : eval read p 4981404 = NetHack.Sokoban12CostPartition.d280 p := by
  change eval read p 4981404 = (if p 134 then NetHack.Sokoban12CostPartition.d279 p else NetHack.Sokoban12CostPartition.d268 p)
  have code : read 4981404 = .branch 134 4784984 4784985 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode268 p, oldNode279 p]
theorem oldNode281 (p : Pattern) : eval read p 4523387 = NetHack.Sokoban12CostPartition.d281 p := by
  change eval read p 4523387 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 4523387 = .branch 158 4391991 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode269 p]
theorem oldNode282 (p : Pattern) : eval read p 4784986 = NetHack.Sokoban12CostPartition.d282 p := by
  change eval read p 4784986 = (if p 141 then NetHack.Sokoban12CostPartition.d281 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 4784986 = .branch 141 4523360 4523387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode281 p]
theorem oldNode283 (p : Pattern) : eval read p 4523388 = NetHack.Sokoban12CostPartition.d283 p := by
  change eval read p 4523388 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d277 p)
  have code : read 4523388 = .branch 158 4457765 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode277 p, oldNode269 p]
theorem oldNode284 (p : Pattern) : eval read p 4784987 = NetHack.Sokoban12CostPartition.d284 p := by
  change eval read p 4784987 = (if p 141 then NetHack.Sokoban12CostPartition.d283 p else NetHack.Sokoban12CostPartition.d181 p)
  have code : read 4784987 = .branch 141 4523373 4523388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode181 p, oldNode283 p]
theorem oldNode285 (p : Pattern) : eval read p 4981405 = NetHack.Sokoban12CostPartition.d285 p := by
  change eval read p 4981405 = (if p 134 then NetHack.Sokoban12CostPartition.d284 p else NetHack.Sokoban12CostPartition.d282 p)
  have code : read 4981405 = .branch 134 4784986 4784987 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode282 p, oldNode284 p]
theorem oldNode286 (p : Pattern) : eval read p 5046744 = NetHack.Sokoban12CostPartition.d286 p := by
  change eval read p 5046744 = (if p 133 then NetHack.Sokoban12CostPartition.d285 p else NetHack.Sokoban12CostPartition.d280 p)
  have code : read 5046744 = .branch 133 4981404 4981405 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode280 p, oldNode285 p]
theorem oldNode287 (p : Pattern) : eval read p 4784988 = NetHack.Sokoban12CostPartition.d287 p := by
  change eval read p 4784988 = (if p 141 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 4784988 = .branch 141 3411913 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode269 p]
theorem oldNode288 (p : Pattern) : eval read p 5046745 = NetHack.Sokoban12CostPartition.d288 p := by
  change eval read p 5046745 = (if p 133 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d285 p)
  have code : read 5046745 = .branch 133 4981405 4784988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode285 p, oldNode287 p]
theorem oldNode289 (p : Pattern) : eval read p 5112163 = NetHack.Sokoban12CostPartition.d289 p := by
  change eval read p 5112163 = (if p 132 then NetHack.Sokoban12CostPartition.d288 p else NetHack.Sokoban12CostPartition.d286 p)
  have code : read 5112163 = .branch 132 5046744 5046745 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode286 p, oldNode288 p]
theorem oldNode290 (p : Pattern) : eval read p 3737612 = NetHack.Sokoban12CostPartition.d290 p := by
  change eval read p 3737612 = (if p 186 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d271 p)
  have code : read 3737612 = .branch 186 3671968 3411918 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode271 p, oldNode260 p]
theorem oldNode291 (p : Pattern) : eval read p 3737613 = NetHack.Sokoban12CostPartition.d291 p := by
  change eval read p 3737613 = (if p 186 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d273 p)
  have code : read 3737613 = .branch 186 3671969 3411919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode273 p, oldNode264 p]
theorem oldNode292 (p : Pattern) : eval read p 3999616 = NetHack.Sokoban12CostPartition.d292 p := by
  change eval read p 3999616 = (if p 168 then NetHack.Sokoban12CostPartition.d291 p else NetHack.Sokoban12CostPartition.d290 p)
  have code : read 3999616 = .branch 168 3737612 3737613 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode290 p, oldNode291 p]
theorem oldNode293 (p : Pattern) : eval read p 4391994 = NetHack.Sokoban12CostPartition.d293 p := by
  change eval read p 4391994 = (if p 160 then NetHack.Sokoban12CostPartition.d292 p else NetHack.Sokoban12CostPartition.d275 p)
  have code : read 4391994 = .branch 160 3999615 3999616 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode275 p, oldNode292 p]
theorem oldNode294 (p : Pattern) : eval read p 4457766 = NetHack.Sokoban12CostPartition.d294 p := by
  change eval read p 4457766 = (if p 159 then NetHack.Sokoban12CostPartition.d293 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 4457766 = .branch 159 4391991 4391994 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode293 p]
theorem oldNode295 (p : Pattern) : eval read p 4523389 = NetHack.Sokoban12CostPartition.d295 p := by
  change eval read p 4523389 = (if p 158 then NetHack.Sokoban12CostPartition.d294 p else NetHack.Sokoban12CostPartition.d267 p)
  have code : read 4523389 = .branch 158 4391991 4457766 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode267 p, oldNode294 p]
end NetHack.Soko12Forward220.Shared
