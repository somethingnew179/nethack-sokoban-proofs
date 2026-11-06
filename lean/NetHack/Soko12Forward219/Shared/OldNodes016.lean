import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode528 (p : Pattern) : eval read p 229392 = NetHack.Sokoban12CostPartition.d528 p := by
  change eval read p 229392 = (if p 192 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 229392 = .branch 192 90113 8192 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode5 p]
theorem oldNode529 (p : Pattern) : eval read p 270352 = NetHack.Sokoban12CostPartition.d529 p := by
  change eval read p 270352 = (if p 186 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 270352 = .branch 186 229381 229392 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode528 p]
theorem oldNode530 (p : Pattern) : eval read p 286746 = NetHack.Sokoban12CostPartition.d530 p := by
  change eval read p 286746 = (if p 168 then NetHack.Sokoban12CostPartition.d529 p else NetHack.Sokoban12CostPartition.d526 p)
  have code : read 286746 = .branch 168 270351 270352 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode526 p, oldNode529 p]
theorem oldNode531 (p : Pattern) : eval read p 319531 = NetHack.Sokoban12CostPartition.d531 p := by
  change eval read p 319531 = (if p 160 then NetHack.Sokoban12CostPartition.d530 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 319531 = .branch 160 286724 286746 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode530 p]
theorem oldNode532 (p : Pattern) : eval read p 360501 = NetHack.Sokoban12CostPartition.d532 p := by
  change eval read p 360501 = (if p 141 then NetHack.Sokoban12CostPartition.d531 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 360501 = .branch 141 319530 319531 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode531 p]
theorem oldNode533 (p : Pattern) : eval read p 319532 = NetHack.Sokoban12CostPartition.d533 p := by
  change eval read p 319532 = (if p 160 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 319532 = .branch 160 229380 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode534 (p : Pattern) : eval read p 262149 = NetHack.Sokoban12CostPartition.d534 p := by
  change eval read p 262149 = (if p 187 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 262149 = .branch 187 229380 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode525 p]
theorem oldNode535 (p : Pattern) : eval read p 270353 = NetHack.Sokoban12CostPartition.d535 p := by
  change eval read p 270353 = (if p 186 then NetHack.Sokoban12CostPartition.d534 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 270353 = .branch 186 229380 262149 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode534 p]
theorem oldNode536 (p : Pattern) : eval read p 319533 = NetHack.Sokoban12CostPartition.d536 p := by
  change eval read p 319533 = (if p 160 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 319533 = .branch 160 270353 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode525 p]
theorem oldNode537 (p : Pattern) : eval read p 327716 = NetHack.Sokoban12CostPartition.d537 p := by
  change eval read p 327716 = (if p 159 then NetHack.Sokoban12CostPartition.d536 p else NetHack.Sokoban12CostPartition.d533 p)
  have code : read 327716 = .branch 159 319532 319533 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode533 p, oldNode536 p]
theorem oldNode538 (p : Pattern) : eval read p 335956 = NetHack.Sokoban12CostPartition.d538 p := by
  change eval read p 335956 = (if p 158 then NetHack.Sokoban12CostPartition.d537 p else NetHack.Sokoban12CostPartition.d533 p)
  have code : read 335956 = .branch 158 319532 327716 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode533 p, oldNode537 p]
theorem oldNode539 (p : Pattern) : eval read p 286747 = NetHack.Sokoban12CostPartition.d539 p := by
  change eval read p 286747 = (if p 168 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d525 p)
  have code : read 286747 = .branch 168 229391 229392 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode525 p, oldNode528 p]
theorem oldNode540 (p : Pattern) : eval read p 319534 = NetHack.Sokoban12CostPartition.d540 p := by
  change eval read p 319534 = (if p 160 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 319534 = .branch 160 286724 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode539 p]
theorem oldNode541 (p : Pattern) : eval read p 262150 = NetHack.Sokoban12CostPartition.d541 p := by
  change eval read p 262150 = (if p 187 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 262150 = .branch 187 229381 229392 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode528 p]
theorem oldNode542 (p : Pattern) : eval read p 270354 = NetHack.Sokoban12CostPartition.d542 p := by
  change eval read p 270354 = (if p 186 then NetHack.Sokoban12CostPartition.d541 p else NetHack.Sokoban12CostPartition.d25 p)
  have code : read 270354 = .branch 186 229381 262150 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode25 p, oldNode541 p]
theorem oldNode543 (p : Pattern) : eval read p 286748 = NetHack.Sokoban12CostPartition.d543 p := by
  change eval read p 286748 = (if p 168 then NetHack.Sokoban12CostPartition.d542 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 286748 = .branch 168 270353 270354 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode542 p]
theorem oldNode544 (p : Pattern) : eval read p 319535 = NetHack.Sokoban12CostPartition.d544 p := by
  change eval read p 319535 = (if p 160 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d543 p)
  have code : read 319535 = .branch 160 286748 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode543 p, oldNode539 p]
theorem oldNode545 (p : Pattern) : eval read p 327717 = NetHack.Sokoban12CostPartition.d545 p := by
  change eval read p 327717 = (if p 159 then NetHack.Sokoban12CostPartition.d544 p else NetHack.Sokoban12CostPartition.d540 p)
  have code : read 327717 = .branch 159 319534 319535 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode540 p, oldNode544 p]
theorem oldNode546 (p : Pattern) : eval read p 335957 = NetHack.Sokoban12CostPartition.d546 p := by
  change eval read p 335957 = (if p 158 then NetHack.Sokoban12CostPartition.d545 p else NetHack.Sokoban12CostPartition.d540 p)
  have code : read 335957 = .branch 158 319534 327717 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode540 p, oldNode545 p]
theorem oldNode547 (p : Pattern) : eval read p 360502 = NetHack.Sokoban12CostPartition.d547 p := by
  change eval read p 360502 = (if p 141 then NetHack.Sokoban12CostPartition.d546 p else NetHack.Sokoban12CostPartition.d538 p)
  have code : read 360502 = .branch 141 335956 335957 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode538 p, oldNode546 p]
theorem oldNode548 (p : Pattern) : eval read p 368715 = NetHack.Sokoban12CostPartition.d548 p := by
  change eval read p 368715 = (if p 134 then NetHack.Sokoban12CostPartition.d547 p else NetHack.Sokoban12CostPartition.d532 p)
  have code : read 368715 = .branch 134 360501 360502 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode532 p, oldNode547 p]
theorem oldNode549 (p : Pattern) : eval read p 335958 = NetHack.Sokoban12CostPartition.d549 p := by
  change eval read p 335958 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 335958 = .branch 158 319530 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode525 p]
theorem oldNode550 (p : Pattern) : eval read p 335959 = NetHack.Sokoban12CostPartition.d550 p := by
  change eval read p 335959 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 335959 = .branch 158 319531 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode539 p]
theorem oldNode551 (p : Pattern) : eval read p 360503 = NetHack.Sokoban12CostPartition.d551 p := by
  change eval read p 360503 = (if p 141 then NetHack.Sokoban12CostPartition.d550 p else NetHack.Sokoban12CostPartition.d549 p)
  have code : read 360503 = .branch 141 335958 335959 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode549 p, oldNode550 p]
end NetHack.Soko12Forward219.Shared
