import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode552 (p : Pattern) : eval read p 335960 = NetHack.Sokoban12CostPartition.d552 p := by
  change eval read p 335960 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d537 p)
  have code : read 335960 = .branch 158 327716 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode537 p, oldNode525 p]
theorem oldNode553 (p : Pattern) : eval read p 335961 = NetHack.Sokoban12CostPartition.d553 p := by
  change eval read p 335961 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d545 p)
  have code : read 335961 = .branch 158 327717 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode545 p, oldNode539 p]
theorem oldNode554 (p : Pattern) : eval read p 360504 = NetHack.Sokoban12CostPartition.d554 p := by
  change eval read p 360504 = (if p 141 then NetHack.Sokoban12CostPartition.d553 p else NetHack.Sokoban12CostPartition.d552 p)
  have code : read 360504 = .branch 141 335960 335961 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode552 p, oldNode553 p]
theorem oldNode555 (p : Pattern) : eval read p 368716 = NetHack.Sokoban12CostPartition.d555 p := by
  change eval read p 368716 = (if p 134 then NetHack.Sokoban12CostPartition.d554 p else NetHack.Sokoban12CostPartition.d551 p)
  have code : read 368716 = .branch 134 360503 360504 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode551 p, oldNode554 p]
theorem oldNode556 (p : Pattern) : eval read p 376910 = NetHack.Sokoban12CostPartition.d556 p := by
  change eval read p 376910 = (if p 133 then NetHack.Sokoban12CostPartition.d555 p else NetHack.Sokoban12CostPartition.d548 p)
  have code : read 376910 = .branch 133 368715 368716 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode548 p, oldNode555 p]
theorem oldNode557 (p : Pattern) : eval read p 360505 = NetHack.Sokoban12CostPartition.d557 p := by
  change eval read p 360505 = (if p 141 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d525 p)
  have code : read 360505 = .branch 141 229391 286747 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode525 p, oldNode539 p]
theorem oldNode558 (p : Pattern) : eval read p 376911 = NetHack.Sokoban12CostPartition.d558 p := by
  change eval read p 376911 = (if p 133 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d555 p)
  have code : read 376911 = .branch 133 368716 360505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode555 p, oldNode557 p]
theorem oldNode559 (p : Pattern) : eval read p 385070 = NetHack.Sokoban12CostPartition.d559 p := by
  change eval read p 385070 = (if p 132 then NetHack.Sokoban12CostPartition.d558 p else NetHack.Sokoban12CostPartition.d556 p)
  have code : read 385070 = .branch 132 376910 376911 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode556 p, oldNode558 p]
theorem oldNode560 (p : Pattern) : eval read p 270355 = NetHack.Sokoban12CostPartition.d560 p := by
  change eval read p 270355 = (if p 186 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d534 p)
  have code : read 270355 = .branch 186 262149 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode534 p, oldNode525 p]
theorem oldNode561 (p : Pattern) : eval read p 319536 = NetHack.Sokoban12CostPartition.d561 p := by
  change eval read p 319536 = (if p 160 then NetHack.Sokoban12CostPartition.d560 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 319536 = .branch 160 270353 270355 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode560 p]
theorem oldNode562 (p : Pattern) : eval read p 327718 = NetHack.Sokoban12CostPartition.d562 p := by
  change eval read p 327718 = (if p 159 then NetHack.Sokoban12CostPartition.d561 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 327718 = .branch 159 319530 319536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode561 p]
theorem oldNode563 (p : Pattern) : eval read p 335962 = NetHack.Sokoban12CostPartition.d563 p := by
  change eval read p 335962 = (if p 158 then NetHack.Sokoban12CostPartition.d562 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 335962 = .branch 158 319530 327718 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode562 p]
theorem oldNode564 (p : Pattern) : eval read p 270356 = NetHack.Sokoban12CostPartition.d564 p := by
  change eval read p 270356 = (if p 186 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d541 p)
  have code : read 270356 = .branch 186 262150 229392 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode541 p, oldNode528 p]
theorem oldNode565 (p : Pattern) : eval read p 286749 = NetHack.Sokoban12CostPartition.d565 p := by
  change eval read p 286749 = (if p 168 then NetHack.Sokoban12CostPartition.d564 p else NetHack.Sokoban12CostPartition.d560 p)
  have code : read 286749 = .branch 168 270355 270356 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode560 p, oldNode564 p]
theorem oldNode566 (p : Pattern) : eval read p 319537 = NetHack.Sokoban12CostPartition.d566 p := by
  change eval read p 319537 = (if p 160 then NetHack.Sokoban12CostPartition.d565 p else NetHack.Sokoban12CostPartition.d543 p)
  have code : read 319537 = .branch 160 286748 286749 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode543 p, oldNode565 p]
theorem oldNode567 (p : Pattern) : eval read p 327719 = NetHack.Sokoban12CostPartition.d567 p := by
  change eval read p 327719 = (if p 159 then NetHack.Sokoban12CostPartition.d566 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 327719 = .branch 159 319531 319537 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode566 p]
theorem oldNode568 (p : Pattern) : eval read p 335963 = NetHack.Sokoban12CostPartition.d568 p := by
  change eval read p 335963 = (if p 158 then NetHack.Sokoban12CostPartition.d567 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 335963 = .branch 158 319531 327719 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode567 p]
theorem oldNode569 (p : Pattern) : eval read p 360506 = NetHack.Sokoban12CostPartition.d569 p := by
  change eval read p 360506 = (if p 141 then NetHack.Sokoban12CostPartition.d568 p else NetHack.Sokoban12CostPartition.d563 p)
  have code : read 360506 = .branch 141 335962 335963 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode563 p, oldNode568 p]
theorem oldNode570 (p : Pattern) : eval read p 368717 = NetHack.Sokoban12CostPartition.d570 p := by
  change eval read p 368717 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d569 p)
  have code : read 368717 = .branch 134 360506 360505 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode569 p, oldNode557 p]
theorem oldNode571 (p : Pattern) : eval read p 319538 = NetHack.Sokoban12CostPartition.d571 p := by
  change eval read p 319538 = (if p 160 then NetHack.Sokoban12CostPartition.d560 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 319538 = .branch 160 229380 270355 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode560 p]
theorem oldNode572 (p : Pattern) : eval read p 327720 = NetHack.Sokoban12CostPartition.d572 p := by
  change eval read p 327720 = (if p 159 then NetHack.Sokoban12CostPartition.d561 p else NetHack.Sokoban12CostPartition.d571 p)
  have code : read 327720 = .branch 159 319538 319536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode571 p, oldNode561 p]
theorem oldNode573 (p : Pattern) : eval read p 335964 = NetHack.Sokoban12CostPartition.d573 p := by
  change eval read p 335964 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d572 p)
  have code : read 335964 = .branch 158 327720 229391 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode572 p, oldNode525 p]
theorem oldNode574 (p : Pattern) : eval read p 319539 = NetHack.Sokoban12CostPartition.d574 p := by
  change eval read p 319539 = (if p 160 then NetHack.Sokoban12CostPartition.d565 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 319539 = .branch 160 286724 286749 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode565 p]
theorem oldNode575 (p : Pattern) : eval read p 327721 = NetHack.Sokoban12CostPartition.d575 p := by
  change eval read p 327721 = (if p 159 then NetHack.Sokoban12CostPartition.d566 p else NetHack.Sokoban12CostPartition.d574 p)
  have code : read 327721 = .branch 159 319539 319537 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode574 p, oldNode566 p]
end NetHack.Soko12Forward219.Shared
