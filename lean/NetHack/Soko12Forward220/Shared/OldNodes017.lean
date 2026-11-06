import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode552 (p : Pattern) : eval read p 4523426 = NetHack.Sokoban12CostPartition.d552 p := by
  change eval read p 4523426 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d537 p)
  have code : read 4523426 = .branch 158 4457778 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode537 p, oldNode525 p]
theorem oldNode553 (p : Pattern) : eval read p 4523427 = NetHack.Sokoban12CostPartition.d553 p := by
  change eval read p 4523427 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d545 p)
  have code : read 4523427 = .branch 158 4457779 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode545 p, oldNode539 p]
theorem oldNode554 (p : Pattern) : eval read p 4785018 = NetHack.Sokoban12CostPartition.d554 p := by
  change eval read p 4785018 = (if p 141 then NetHack.Sokoban12CostPartition.d553 p else NetHack.Sokoban12CostPartition.d552 p)
  have code : read 4785018 = .branch 141 4523426 4523427 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode552 p, oldNode553 p]
theorem oldNode555 (p : Pattern) : eval read p 4981431 = NetHack.Sokoban12CostPartition.d555 p := by
  change eval read p 4981431 = (if p 134 then NetHack.Sokoban12CostPartition.d554 p else NetHack.Sokoban12CostPartition.d551 p)
  have code : read 4981431 = .branch 134 4785017 4785018 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode551 p, oldNode554 p]
theorem oldNode556 (p : Pattern) : eval read p 5046770 = NetHack.Sokoban12CostPartition.d556 p := by
  change eval read p 5046770 = (if p 133 then NetHack.Sokoban12CostPartition.d555 p else NetHack.Sokoban12CostPartition.d548 p)
  have code : read 5046770 = .branch 133 4981430 4981431 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode548 p, oldNode555 p]
theorem oldNode557 (p : Pattern) : eval read p 4785019 = NetHack.Sokoban12CostPartition.d557 p := by
  change eval read p 4785019 = (if p 141 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d525 p)
  have code : read 4785019 = .branch 141 3411921 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode525 p, oldNode539 p]
theorem oldNode558 (p : Pattern) : eval read p 5046771 = NetHack.Sokoban12CostPartition.d558 p := by
  change eval read p 5046771 = (if p 133 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d555 p)
  have code : read 5046771 = .branch 133 4981431 4785019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode555 p, oldNode557 p]
theorem oldNode559 (p : Pattern) : eval read p 5112177 = NetHack.Sokoban12CostPartition.d559 p := by
  change eval read p 5112177 = (if p 132 then NetHack.Sokoban12CostPartition.d558 p else NetHack.Sokoban12CostPartition.d556 p)
  have code : read 5112177 = .branch 132 5046770 5046771 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode556 p, oldNode558 p]
theorem oldNode560 (p : Pattern) : eval read p 3737618 = NetHack.Sokoban12CostPartition.d560 p := by
  change eval read p 3737618 = (if p 186 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d534 p)
  have code : read 3737618 = .branch 186 3671970 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode534 p, oldNode525 p]
theorem oldNode561 (p : Pattern) : eval read p 4392020 = NetHack.Sokoban12CostPartition.d561 p := by
  change eval read p 4392020 = (if p 160 then NetHack.Sokoban12CostPartition.d560 p else NetHack.Sokoban12CostPartition.d535 p)
  have code : read 4392020 = .branch 160 3737616 3737618 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode535 p, oldNode560 p]
theorem oldNode562 (p : Pattern) : eval read p 4457780 = NetHack.Sokoban12CostPartition.d562 p := by
  change eval read p 4457780 = (if p 159 then NetHack.Sokoban12CostPartition.d561 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 4457780 = .branch 159 4392014 4392020 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode561 p]
theorem oldNode563 (p : Pattern) : eval read p 4523428 = NetHack.Sokoban12CostPartition.d563 p := by
  change eval read p 4523428 = (if p 158 then NetHack.Sokoban12CostPartition.d562 p else NetHack.Sokoban12CostPartition.d527 p)
  have code : read 4523428 = .branch 158 4392014 4457780 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode527 p, oldNode562 p]
theorem oldNode564 (p : Pattern) : eval read p 3737619 = NetHack.Sokoban12CostPartition.d564 p := by
  change eval read p 3737619 = (if p 186 then NetHack.Sokoban12CostPartition.d528 p else NetHack.Sokoban12CostPartition.d541 p)
  have code : read 3737619 = .branch 186 3671971 3411923 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode541 p, oldNode528 p]
theorem oldNode565 (p : Pattern) : eval read p 3999632 = NetHack.Sokoban12CostPartition.d565 p := by
  change eval read p 3999632 = (if p 168 then NetHack.Sokoban12CostPartition.d564 p else NetHack.Sokoban12CostPartition.d560 p)
  have code : read 3999632 = .branch 168 3737618 3737619 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode560 p, oldNode564 p]
theorem oldNode566 (p : Pattern) : eval read p 4392021 = NetHack.Sokoban12CostPartition.d566 p := by
  change eval read p 4392021 = (if p 160 then NetHack.Sokoban12CostPartition.d565 p else NetHack.Sokoban12CostPartition.d543 p)
  have code : read 4392021 = .branch 160 3999631 3999632 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode543 p, oldNode565 p]
theorem oldNode567 (p : Pattern) : eval read p 4457781 = NetHack.Sokoban12CostPartition.d567 p := by
  change eval read p 4457781 = (if p 159 then NetHack.Sokoban12CostPartition.d566 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 4457781 = .branch 159 4392015 4392021 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode566 p]
theorem oldNode568 (p : Pattern) : eval read p 4523429 = NetHack.Sokoban12CostPartition.d568 p := by
  change eval read p 4523429 = (if p 158 then NetHack.Sokoban12CostPartition.d567 p else NetHack.Sokoban12CostPartition.d531 p)
  have code : read 4523429 = .branch 158 4392015 4457781 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode531 p, oldNode567 p]
theorem oldNode569 (p : Pattern) : eval read p 4785020 = NetHack.Sokoban12CostPartition.d569 p := by
  change eval read p 4785020 = (if p 141 then NetHack.Sokoban12CostPartition.d568 p else NetHack.Sokoban12CostPartition.d563 p)
  have code : read 4785020 = .branch 141 4523428 4523429 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode563 p, oldNode568 p]
theorem oldNode570 (p : Pattern) : eval read p 4981432 = NetHack.Sokoban12CostPartition.d570 p := by
  change eval read p 4981432 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d569 p)
  have code : read 4981432 = .branch 134 4785020 4785019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode569 p, oldNode557 p]
theorem oldNode571 (p : Pattern) : eval read p 4392022 = NetHack.Sokoban12CostPartition.d571 p := by
  change eval read p 4392022 = (if p 160 then NetHack.Sokoban12CostPartition.d560 p else NetHack.Sokoban12CostPartition.d24 p)
  have code : read 4392022 = .branch 160 3411920 3737618 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode24 p, oldNode560 p]
theorem oldNode572 (p : Pattern) : eval read p 4457782 = NetHack.Sokoban12CostPartition.d572 p := by
  change eval read p 4457782 = (if p 159 then NetHack.Sokoban12CostPartition.d561 p else NetHack.Sokoban12CostPartition.d571 p)
  have code : read 4457782 = .branch 159 4392022 4392020 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode571 p, oldNode561 p]
theorem oldNode573 (p : Pattern) : eval read p 4523430 = NetHack.Sokoban12CostPartition.d573 p := by
  change eval read p 4523430 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d572 p)
  have code : read 4523430 = .branch 158 4457782 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode572 p, oldNode525 p]
theorem oldNode574 (p : Pattern) : eval read p 4392023 = NetHack.Sokoban12CostPartition.d574 p := by
  change eval read p 4392023 = (if p 160 then NetHack.Sokoban12CostPartition.d565 p else NetHack.Sokoban12CostPartition.d26 p)
  have code : read 4392023 = .branch 160 3999628 3999632 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode26 p, oldNode565 p]
theorem oldNode575 (p : Pattern) : eval read p 4457783 = NetHack.Sokoban12CostPartition.d575 p := by
  change eval read p 4457783 = (if p 159 then NetHack.Sokoban12CostPartition.d566 p else NetHack.Sokoban12CostPartition.d574 p)
  have code : read 4457783 = .branch 159 4392023 4392021 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode574 p, oldNode566 p]
end NetHack.Soko12Forward220.Shared
