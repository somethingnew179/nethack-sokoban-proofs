import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode296 (p : Pattern) : eval read p 4784989 = NetHack.Sokoban12CostPartition.d296 p := by
  change eval read p 4784989 = (if p 141 then NetHack.Sokoban12CostPartition.d295 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 4784989 = .branch 141 4523374 4523389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode295 p]
theorem oldNode297 (p : Pattern) : eval read p 4981406 = NetHack.Sokoban12CostPartition.d297 p := by
  change eval read p 4981406 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d296 p)
  have code : read 4981406 = .branch 134 4784989 4784988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode296 p, oldNode287 p]
theorem oldNode298 (p : Pattern) : eval read p 4391995 = NetHack.Sokoban12CostPartition.d298 p := by
  change eval read p 4391995 = (if p 160 then NetHack.Sokoban12CostPartition.d292 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 4391995 = .branch 160 3999612 3999616 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode292 p]
theorem oldNode299 (p : Pattern) : eval read p 4457767 = NetHack.Sokoban12CostPartition.d299 p := by
  change eval read p 4457767 = (if p 159 then NetHack.Sokoban12CostPartition.d293 p else NetHack.Sokoban12CostPartition.d298 p)
  have code : read 4457767 = .branch 159 4391995 4391994 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode298 p, oldNode293 p]
theorem oldNode300 (p : Pattern) : eval read p 4523390 = NetHack.Sokoban12CostPartition.d300 p := by
  change eval read p 4523390 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d299 p)
  have code : read 4523390 = .branch 158 4457767 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode299 p, oldNode269 p]
theorem oldNode301 (p : Pattern) : eval read p 4784990 = NetHack.Sokoban12CostPartition.d301 p := by
  change eval read p 4784990 = (if p 141 then NetHack.Sokoban12CostPartition.d300 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 4784990 = .branch 141 4523375 4523390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode300 p]
theorem oldNode302 (p : Pattern) : eval read p 4981407 = NetHack.Sokoban12CostPartition.d302 p := by
  change eval read p 4981407 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d301 p)
  have code : read 4981407 = .branch 134 4784990 4784988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode301 p, oldNode287 p]
theorem oldNode303 (p : Pattern) : eval read p 5046746 = NetHack.Sokoban12CostPartition.d303 p := by
  change eval read p 5046746 = (if p 133 then NetHack.Sokoban12CostPartition.d302 p else NetHack.Sokoban12CostPartition.d297 p)
  have code : read 5046746 = .branch 133 4981406 4981407 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode297 p, oldNode302 p]
theorem oldNode304 (p : Pattern) : eval read p 4523391 = NetHack.Sokoban12CostPartition.d304 p := by
  change eval read p 4523391 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d294 p)
  have code : read 4523391 = .branch 158 4457766 3999614 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode294 p, oldNode269 p]
theorem oldNode305 (p : Pattern) : eval read p 4784991 = NetHack.Sokoban12CostPartition.d305 p := by
  change eval read p 4784991 = (if p 141 then NetHack.Sokoban12CostPartition.d304 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 4784991 = .branch 141 4523376 4523391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode304 p]
theorem oldNode306 (p : Pattern) : eval read p 4981408 = NetHack.Sokoban12CostPartition.d306 p := by
  change eval read p 4981408 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d305 p)
  have code : read 4981408 = .branch 134 4784991 4784988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode305 p, oldNode287 p]
theorem oldNode307 (p : Pattern) : eval read p 5046747 = NetHack.Sokoban12CostPartition.d307 p := by
  change eval read p 5046747 = (if p 133 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d306 p)
  have code : read 5046747 = .branch 133 4981408 4784988 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode306 p, oldNode287 p]
theorem oldNode308 (p : Pattern) : eval read p 5112164 = NetHack.Sokoban12CostPartition.d308 p := by
  change eval read p 5112164 = (if p 132 then NetHack.Sokoban12CostPartition.d307 p else NetHack.Sokoban12CostPartition.d303 p)
  have code : read 5112164 = .branch 132 5046746 5046747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode303 p, oldNode307 p]
theorem oldNode309 (p : Pattern) : eval read p 5439692 = NetHack.Sokoban12CostPartition.d309 p := by
  change eval read p 5439692 = (if p 108 then NetHack.Sokoban12CostPartition.d308 p else NetHack.Sokoban12CostPartition.d289 p)
  have code : read 5439692 = .branch 108 5112163 5112164 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode289 p, oldNode308 p]
theorem oldNode315 (p : Pattern) : eval read p 5046748 = NetHack.Sokoban12CostPartition.d315 p := by
  change eval read p 5046748 = (if p 133 then NetHack.Sokoban12CostPartition.d242 p else NetHack.Sokoban12CostPartition.d232 p)
  have code : read 5046748 = .branch 133 4981398 4981400 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode232 p, oldNode242 p]
theorem oldNode316 (p : Pattern) : eval read p 5112165 = NetHack.Sokoban12CostPartition.d316 p := by
  change eval read p 5112165 = (if p 132 then NetHack.Sokoban12CostPartition.d244 p else NetHack.Sokoban12CostPartition.d315 p)
  have code : read 5112165 = .branch 132 5046748 5046741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode315 p, oldNode244 p]
theorem oldNode317 (p : Pattern) : eval read p 5046749 = NetHack.Sokoban12CostPartition.d317 p := by
  change eval read p 5046749 = (if p 133 then NetHack.Sokoban12CostPartition.d251 p else NetHack.Sokoban12CostPartition.d71 p)
  have code : read 5046749 = .branch 133 4981386 4981402 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode71 p, oldNode251 p]
theorem oldNode318 (p : Pattern) : eval read p 5112166 = NetHack.Sokoban12CostPartition.d318 p := by
  change eval read p 5112166 = (if p 132 then NetHack.Sokoban12CostPartition.d256 p else NetHack.Sokoban12CostPartition.d317 p)
  have code : read 5112166 = .branch 132 5046749 5046743 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode317 p, oldNode256 p]
theorem oldNode319 (p : Pattern) : eval read p 5439693 = NetHack.Sokoban12CostPartition.d319 p := by
  change eval read p 5439693 = (if p 108 then NetHack.Sokoban12CostPartition.d318 p else NetHack.Sokoban12CostPartition.d316 p)
  have code : read 5439693 = .branch 108 5112165 5112166 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode316 p, oldNode318 p]
theorem oldNode335 (p : Pattern) : eval read p 4784992 = NetHack.Sokoban12CostPartition.d335 p := by
  change eval read p 4784992 = (if p 141 then NetHack.Sokoban12CostPartition.d116 p else NetHack.Sokoban12CostPartition.d114 p)
  have code : read 4784992 = .branch 141 4457753 4457754 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode114 p, oldNode116 p]
theorem oldNode336 (p : Pattern) : eval read p 4784993 = NetHack.Sokoban12CostPartition.d336 p := by
  change eval read p 4784993 = (if p 141 then NetHack.Sokoban12CostPartition.d110 p else NetHack.Sokoban12CostPartition.d107 p)
  have code : read 4784993 = .branch 141 4457751 4457752 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode107 p, oldNode110 p]
theorem oldNode337 (p : Pattern) : eval read p 4981409 = NetHack.Sokoban12CostPartition.d337 p := by
  change eval read p 4981409 = (if p 134 then NetHack.Sokoban12CostPartition.d336 p else NetHack.Sokoban12CostPartition.d335 p)
  have code : read 4981409 = .branch 134 4784992 4784993 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode335 p, oldNode336 p]
theorem oldNode338 (p : Pattern) : eval read p 4523392 = NetHack.Sokoban12CostPartition.d338 p := by
  change eval read p 4523392 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d114 p)
  have code : read 4523392 = .branch 158 4457753 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode114 p, oldNode55 p]
theorem oldNode339 (p : Pattern) : eval read p 4523393 = NetHack.Sokoban12CostPartition.d339 p := by
  change eval read p 4523393 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d116 p)
  have code : read 4523393 = .branch 158 4457754 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode116 p, oldNode65 p]
end NetHack.Soko12Forward220.Shared
