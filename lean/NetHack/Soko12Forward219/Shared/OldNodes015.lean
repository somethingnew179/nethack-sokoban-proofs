import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode504 (p : Pattern) : eval read p 360497 = NetHack.Sokoban12CostPartition.d504 p := by
  change eval read p 360497 = (if p 141 then NetHack.Sokoban12CostPartition.d503 p else NetHack.Sokoban12CostPartition.d501 p)
  have code : read 360497 = .branch 141 319526 319527 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode501 p, oldNode503 p]
theorem oldNode505 (p : Pattern) : eval read p 319528 = NetHack.Sokoban12CostPartition.d505 p := by
  change eval read p 319528 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 319528 = .branch 160 262145 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode55 p]
theorem oldNode506 (p : Pattern) : eval read p 319529 = NetHack.Sokoban12CostPartition.d506 p := by
  change eval read p 319529 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d502 p)
  have code : read 319529 = .branch 160 286745 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode502 p, oldNode65 p]
theorem oldNode507 (p : Pattern) : eval read p 360498 = NetHack.Sokoban12CostPartition.d507 p := by
  change eval read p 360498 = (if p 141 then NetHack.Sokoban12CostPartition.d506 p else NetHack.Sokoban12CostPartition.d505 p)
  have code : read 360498 = .branch 141 319528 319529 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode505 p, oldNode506 p]
theorem oldNode508 (p : Pattern) : eval read p 368711 = NetHack.Sokoban12CostPartition.d508 p := by
  change eval read p 368711 = (if p 134 then NetHack.Sokoban12CostPartition.d507 p else NetHack.Sokoban12CostPartition.d504 p)
  have code : read 368711 = .branch 134 360497 360498 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode504 p, oldNode507 p]
theorem oldNode509 (p : Pattern) : eval read p 335952 = NetHack.Sokoban12CostPartition.d509 p := by
  change eval read p 335952 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d501 p)
  have code : read 335952 = .branch 158 319526 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode501 p, oldNode55 p]
theorem oldNode510 (p : Pattern) : eval read p 335953 = NetHack.Sokoban12CostPartition.d510 p := by
  change eval read p 335953 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d503 p)
  have code : read 335953 = .branch 158 319527 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode503 p, oldNode65 p]
theorem oldNode511 (p : Pattern) : eval read p 360499 = NetHack.Sokoban12CostPartition.d511 p := by
  change eval read p 360499 = (if p 141 then NetHack.Sokoban12CostPartition.d510 p else NetHack.Sokoban12CostPartition.d509 p)
  have code : read 360499 = .branch 141 335952 335953 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode509 p, oldNode510 p]
theorem oldNode512 (p : Pattern) : eval read p 335954 = NetHack.Sokoban12CostPartition.d512 p := by
  change eval read p 335954 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d505 p)
  have code : read 335954 = .branch 158 319528 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode505 p, oldNode55 p]
theorem oldNode513 (p : Pattern) : eval read p 335955 = NetHack.Sokoban12CostPartition.d513 p := by
  change eval read p 335955 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d506 p)
  have code : read 335955 = .branch 158 319529 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode506 p, oldNode65 p]
theorem oldNode514 (p : Pattern) : eval read p 360500 = NetHack.Sokoban12CostPartition.d514 p := by
  change eval read p 360500 = (if p 141 then NetHack.Sokoban12CostPartition.d513 p else NetHack.Sokoban12CostPartition.d512 p)
  have code : read 360500 = .branch 141 335954 335955 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode512 p, oldNode513 p]
theorem oldNode515 (p : Pattern) : eval read p 368712 = NetHack.Sokoban12CostPartition.d515 p := by
  change eval read p 368712 = (if p 134 then NetHack.Sokoban12CostPartition.d514 p else NetHack.Sokoban12CostPartition.d511 p)
  have code : read 368712 = .branch 134 360499 360500 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode511 p, oldNode514 p]
theorem oldNode516 (p : Pattern) : eval read p 376906 = NetHack.Sokoban12CostPartition.d516 p := by
  change eval read p 376906 = (if p 133 then NetHack.Sokoban12CostPartition.d515 p else NetHack.Sokoban12CostPartition.d508 p)
  have code : read 376906 = .branch 133 368711 368712 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode508 p, oldNode515 p]
theorem oldNode517 (p : Pattern) : eval read p 376907 = NetHack.Sokoban12CostPartition.d517 p := by
  change eval read p 376907 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d515 p)
  have code : read 376907 = .branch 133 368712 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode515 p, oldNode66 p]
theorem oldNode518 (p : Pattern) : eval read p 385068 = NetHack.Sokoban12CostPartition.d518 p := by
  change eval read p 385068 = (if p 132 then NetHack.Sokoban12CostPartition.d517 p else NetHack.Sokoban12CostPartition.d516 p)
  have code : read 385068 = .branch 132 376906 376907 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode516 p, oldNode517 p]
theorem oldNode519 (p : Pattern) : eval read p 368713 = NetHack.Sokoban12CostPartition.d519 p := by
  change eval read p 368713 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d504 p)
  have code : read 368713 = .branch 134 360497 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode504 p, oldNode66 p]
theorem oldNode520 (p : Pattern) : eval read p 368714 = NetHack.Sokoban12CostPartition.d520 p := by
  change eval read p 368714 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d511 p)
  have code : read 368714 = .branch 134 360499 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode511 p, oldNode66 p]
theorem oldNode521 (p : Pattern) : eval read p 376908 = NetHack.Sokoban12CostPartition.d521 p := by
  change eval read p 376908 = (if p 133 then NetHack.Sokoban12CostPartition.d520 p else NetHack.Sokoban12CostPartition.d519 p)
  have code : read 376908 = .branch 133 368713 368714 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode519 p, oldNode520 p]
theorem oldNode522 (p : Pattern) : eval read p 376909 = NetHack.Sokoban12CostPartition.d522 p := by
  change eval read p 376909 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d520 p)
  have code : read 376909 = .branch 133 368714 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode520 p, oldNode66 p]
theorem oldNode523 (p : Pattern) : eval read p 385069 = NetHack.Sokoban12CostPartition.d523 p := by
  change eval read p 385069 = (if p 132 then NetHack.Sokoban12CostPartition.d522 p else NetHack.Sokoban12CostPartition.d521 p)
  have code : read 385069 = .branch 132 376908 376909 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode521 p, oldNode522 p]
theorem oldNode524 (p : Pattern) : eval read p 409624 = NetHack.Sokoban12CostPartition.d524 p := by
  change eval read p 409624 = (if p 108 then NetHack.Sokoban12CostPartition.d523 p else NetHack.Sokoban12CostPartition.d518 p)
  have code : read 409624 = .branch 108 385068 385069 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode518 p, oldNode523 p]
theorem oldNode525 (p : Pattern) : eval read p 229391 = NetHack.Sokoban12CostPartition.d525 p := by
  change eval read p 229391 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 229391 = .branch 192 2 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode526 (p : Pattern) : eval read p 270351 = NetHack.Sokoban12CostPartition.d526 p := by
  change eval read p 270351 = (if p 186 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 270351 = .branch 186 229380 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode527 (p : Pattern) : eval read p 319530 = NetHack.Sokoban12CostPartition.d527 p := by
  change eval read p 319530 = (if p 160 then NetHack.Sokoban12CostPartition.d526 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 319530 = .branch 160 229380 270351 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode526 p]
end NetHack.Soko12Forward219.Shared
