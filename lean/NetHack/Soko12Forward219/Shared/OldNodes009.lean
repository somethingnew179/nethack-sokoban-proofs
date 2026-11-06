import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode296 (p : Pattern) : eval read p 360475 = NetHack.Sokoban12CostPartition.d296 p := by
  change eval read p 360475 = (if p 141 then NetHack.Sokoban12CostPartition.d295 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 360475 = .branch 141 335897 335914 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode295 p]
theorem oldNode297 (p : Pattern) : eval read p 368675 = NetHack.Sokoban12CostPartition.d297 p := by
  change eval read p 368675 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d296 p)
  have code : read 368675 = .branch 134 360475 360474 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode296 p, oldNode287 p]
theorem oldNode298 (p : Pattern) : eval read p 319507 = NetHack.Sokoban12CostPartition.d298 p := by
  change eval read p 319507 = (if p 160 then NetHack.Sokoban12CostPartition.d292 p else NetHack.Sokoban12CostPartition.d19 p)
  have code : read 319507 = .branch 160 286721 286736 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode19 p, oldNode292 p]
theorem oldNode299 (p : Pattern) : eval read p 327703 = NetHack.Sokoban12CostPartition.d299 p := by
  change eval read p 327703 = (if p 159 then NetHack.Sokoban12CostPartition.d293 p else NetHack.Sokoban12CostPartition.d298 p)
  have code : read 327703 = .branch 159 319507 319506 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode298 p, oldNode293 p]
theorem oldNode300 (p : Pattern) : eval read p 335915 = NetHack.Sokoban12CostPartition.d300 p := by
  change eval read p 335915 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d299 p)
  have code : read 335915 = .branch 158 327703 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode299 p, oldNode269 p]
theorem oldNode301 (p : Pattern) : eval read p 360476 = NetHack.Sokoban12CostPartition.d301 p := by
  change eval read p 360476 = (if p 141 then NetHack.Sokoban12CostPartition.d300 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 360476 = .branch 141 335898 335915 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode300 p]
theorem oldNode302 (p : Pattern) : eval read p 368676 = NetHack.Sokoban12CostPartition.d302 p := by
  change eval read p 368676 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d301 p)
  have code : read 368676 = .branch 134 360476 360474 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode301 p, oldNode287 p]
theorem oldNode303 (p : Pattern) : eval read p 376868 = NetHack.Sokoban12CostPartition.d303 p := by
  change eval read p 376868 = (if p 133 then NetHack.Sokoban12CostPartition.d302 p else NetHack.Sokoban12CostPartition.d297 p)
  have code : read 376868 = .branch 133 368675 368676 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode297 p, oldNode302 p]
theorem oldNode304 (p : Pattern) : eval read p 335916 = NetHack.Sokoban12CostPartition.d304 p := by
  change eval read p 335916 = (if p 158 then NetHack.Sokoban12CostPartition.d269 p else NetHack.Sokoban12CostPartition.d294 p)
  have code : read 335916 = .branch 158 327702 286734 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode294 p, oldNode269 p]
theorem oldNode305 (p : Pattern) : eval read p 360477 = NetHack.Sokoban12CostPartition.d305 p := by
  change eval read p 360477 = (if p 141 then NetHack.Sokoban12CostPartition.d304 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 360477 = .branch 141 335899 335916 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode304 p]
theorem oldNode306 (p : Pattern) : eval read p 368677 = NetHack.Sokoban12CostPartition.d306 p := by
  change eval read p 368677 = (if p 134 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d305 p)
  have code : read 368677 = .branch 134 360477 360474 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode305 p, oldNode287 p]
theorem oldNode307 (p : Pattern) : eval read p 376869 = NetHack.Sokoban12CostPartition.d307 p := by
  change eval read p 376869 = (if p 133 then NetHack.Sokoban12CostPartition.d287 p else NetHack.Sokoban12CostPartition.d306 p)
  have code : read 376869 = .branch 133 368677 360474 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode306 p, oldNode287 p]
theorem oldNode308 (p : Pattern) : eval read p 385047 = NetHack.Sokoban12CostPartition.d308 p := by
  change eval read p 385047 = (if p 132 then NetHack.Sokoban12CostPartition.d307 p else NetHack.Sokoban12CostPartition.d303 p)
  have code : read 385047 = .branch 132 376868 376869 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode303 p, oldNode307 p]
theorem oldNode309 (p : Pattern) : eval read p 409613 = NetHack.Sokoban12CostPartition.d309 p := by
  change eval read p 409613 = (if p 108 then NetHack.Sokoban12CostPartition.d308 p else NetHack.Sokoban12CostPartition.d289 p)
  have code : read 409613 = .branch 108 385046 385047 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode289 p, oldNode308 p]
theorem oldNode315 (p : Pattern) : eval read p 376872 = NetHack.Sokoban12CostPartition.d315 p := by
  change eval read p 376872 = (if p 133 then NetHack.Sokoban12CostPartition.d242 p else NetHack.Sokoban12CostPartition.d232 p)
  have code : read 376872 = .branch 133 368667 368669 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode232 p, oldNode242 p]
theorem oldNode316 (p : Pattern) : eval read p 385050 = NetHack.Sokoban12CostPartition.d316 p := by
  change eval read p 385050 = (if p 132 then NetHack.Sokoban12CostPartition.d244 p else NetHack.Sokoban12CostPartition.d315 p)
  have code : read 385050 = .branch 132 376872 376863 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode315 p, oldNode244 p]
theorem oldNode317 (p : Pattern) : eval read p 376873 = NetHack.Sokoban12CostPartition.d317 p := by
  change eval read p 376873 = (if p 133 then NetHack.Sokoban12CostPartition.d251 p else NetHack.Sokoban12CostPartition.d71 p)
  have code : read 376873 = .branch 133 368643 368671 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode71 p, oldNode251 p]
theorem oldNode318 (p : Pattern) : eval read p 385051 = NetHack.Sokoban12CostPartition.d318 p := by
  change eval read p 385051 = (if p 132 then NetHack.Sokoban12CostPartition.d256 p else NetHack.Sokoban12CostPartition.d317 p)
  have code : read 385051 = .branch 132 376873 376865 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode317 p, oldNode256 p]
theorem oldNode319 (p : Pattern) : eval read p 409615 = NetHack.Sokoban12CostPartition.d319 p := by
  change eval read p 409615 = (if p 108 then NetHack.Sokoban12CostPartition.d318 p else NetHack.Sokoban12CostPartition.d316 p)
  have code : read 409615 = .branch 108 385050 385051 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode316 p, oldNode318 p]
theorem oldNode335 (p : Pattern) : eval read p 360478 = NetHack.Sokoban12CostPartition.d335 p := by
  change eval read p 360478 = (if p 141 then NetHack.Sokoban12CostPartition.d116 p else NetHack.Sokoban12CostPartition.d114 p)
  have code : read 360478 = .branch 141 327689 327690 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode114 p, oldNode116 p]
theorem oldNode336 (p : Pattern) : eval read p 360479 = NetHack.Sokoban12CostPartition.d336 p := by
  change eval read p 360479 = (if p 141 then NetHack.Sokoban12CostPartition.d110 p else NetHack.Sokoban12CostPartition.d107 p)
  have code : read 360479 = .branch 141 327687 327688 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode107 p, oldNode110 p]
theorem oldNode337 (p : Pattern) : eval read p 368683 = NetHack.Sokoban12CostPartition.d337 p := by
  change eval read p 368683 = (if p 134 then NetHack.Sokoban12CostPartition.d336 p else NetHack.Sokoban12CostPartition.d335 p)
  have code : read 368683 = .branch 134 360478 360479 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode335 p, oldNode336 p]
theorem oldNode338 (p : Pattern) : eval read p 335919 = NetHack.Sokoban12CostPartition.d338 p := by
  change eval read p 335919 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d114 p)
  have code : read 335919 = .branch 158 327689 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode114 p, oldNode55 p]
theorem oldNode339 (p : Pattern) : eval read p 335920 = NetHack.Sokoban12CostPartition.d339 p := by
  change eval read p 335920 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d116 p)
  have code : read 335920 = .branch 158 327690 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode116 p, oldNode65 p]
end NetHack.Soko12Forward219.Shared
