import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode576 (p : Pattern) : eval read p 4523431 = NetHack.Sokoban12CostPartition.d576 p := by
  change eval read p 4523431 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d575 p)
  have code : read 4523431 = .branch 158 4457783 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode575 p, oldNode539 p]
theorem oldNode577 (p : Pattern) : eval read p 4785021 = NetHack.Sokoban12CostPartition.d577 p := by
  change eval read p 4785021 = (if p 141 then NetHack.Sokoban12CostPartition.d576 p else NetHack.Sokoban12CostPartition.d573 p)
  have code : read 4785021 = .branch 141 4523430 4523431 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode573 p, oldNode576 p]
theorem oldNode578 (p : Pattern) : eval read p 4981433 = NetHack.Sokoban12CostPartition.d578 p := by
  change eval read p 4981433 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d577 p)
  have code : read 4981433 = .branch 134 4785021 4785019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode577 p, oldNode557 p]
theorem oldNode579 (p : Pattern) : eval read p 5046772 = NetHack.Sokoban12CostPartition.d579 p := by
  change eval read p 5046772 = (if p 133 then NetHack.Sokoban12CostPartition.d578 p else NetHack.Sokoban12CostPartition.d570 p)
  have code : read 5046772 = .branch 133 4981432 4981433 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode570 p, oldNode578 p]
theorem oldNode580 (p : Pattern) : eval read p 4523432 = NetHack.Sokoban12CostPartition.d580 p := by
  change eval read p 4523432 = (if p 158 then NetHack.Sokoban12CostPartition.d525 p else NetHack.Sokoban12CostPartition.d562 p)
  have code : read 4523432 = .branch 158 4457780 3411921 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode562 p, oldNode525 p]
theorem oldNode581 (p : Pattern) : eval read p 4523433 = NetHack.Sokoban12CostPartition.d581 p := by
  change eval read p 4523433 = (if p 158 then NetHack.Sokoban12CostPartition.d539 p else NetHack.Sokoban12CostPartition.d567 p)
  have code : read 4523433 = .branch 158 4457781 3999630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode567 p, oldNode539 p]
theorem oldNode582 (p : Pattern) : eval read p 4785022 = NetHack.Sokoban12CostPartition.d582 p := by
  change eval read p 4785022 = (if p 141 then NetHack.Sokoban12CostPartition.d581 p else NetHack.Sokoban12CostPartition.d580 p)
  have code : read 4785022 = .branch 141 4523432 4523433 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode580 p, oldNode581 p]
theorem oldNode583 (p : Pattern) : eval read p 4981434 = NetHack.Sokoban12CostPartition.d583 p := by
  change eval read p 4981434 = (if p 134 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d582 p)
  have code : read 4981434 = .branch 134 4785022 4785019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode582 p, oldNode557 p]
theorem oldNode584 (p : Pattern) : eval read p 5046773 = NetHack.Sokoban12CostPartition.d584 p := by
  change eval read p 5046773 = (if p 133 then NetHack.Sokoban12CostPartition.d557 p else NetHack.Sokoban12CostPartition.d583 p)
  have code : read 5046773 = .branch 133 4981434 4785019 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode583 p, oldNode557 p]
theorem oldNode585 (p : Pattern) : eval read p 5112178 = NetHack.Sokoban12CostPartition.d585 p := by
  change eval read p 5112178 = (if p 132 then NetHack.Sokoban12CostPartition.d584 p else NetHack.Sokoban12CostPartition.d579 p)
  have code : read 5112178 = .branch 132 5046772 5046773 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode579 p, oldNode584 p]
theorem oldNode586 (p : Pattern) : eval read p 5439699 = NetHack.Sokoban12CostPartition.d586 p := by
  change eval read p 5439699 = (if p 108 then NetHack.Sokoban12CostPartition.d585 p else NetHack.Sokoban12CostPartition.d559 p)
  have code : read 5439699 = .branch 108 5112177 5112178 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode559 p, oldNode585 p]
theorem oldNode587 (p : Pattern) : eval read p 3347241 = NetHack.Sokoban12CostPartition.d587 p := by
  change eval read p 3347241 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3347241 = .branch 193 2 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode5 p]
theorem oldNode588 (p : Pattern) : eval read p 3411926 = NetHack.Sokoban12CostPartition.d588 p := by
  change eval read p 3411926 = (if p 192 then NetHack.Sokoban12CostPartition.d587 p else NetHack.Sokoban12CostPartition.d54 p)
  have code : read 3411926 = .branch 192 3347233 3347241 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode54 p, oldNode587 p]
theorem oldNode589 (p : Pattern) : eval read p 3737620 = NetHack.Sokoban12CostPartition.d589 p := by
  change eval read p 3737620 = (if p 186 then NetHack.Sokoban12CostPartition.d588 p else NetHack.Sokoban12CostPartition.d29 p)
  have code : read 3737620 = .branch 186 3411924 3411926 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode29 p, oldNode588 p]
theorem oldNode590 (p : Pattern) : eval read p 3411927 = NetHack.Sokoban12CostPartition.d590 p := by
  change eval read p 3411927 = (if p 192 then NetHack.Sokoban12CostPartition.d587 p else NetHack.Sokoban12CostPartition.d259 p)
  have code : read 3411927 = .branch 192 3347238 3347241 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode259 p, oldNode587 p]
theorem oldNode591 (p : Pattern) : eval read p 3737621 = NetHack.Sokoban12CostPartition.d591 p := by
  change eval read p 3737621 = (if p 186 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d30 p)
  have code : read 3737621 = .branch 186 3411925 3411927 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode30 p, oldNode590 p]
theorem oldNode592 (p : Pattern) : eval read p 3999634 = NetHack.Sokoban12CostPartition.d592 p := by
  change eval read p 3999634 = (if p 168 then NetHack.Sokoban12CostPartition.d591 p else NetHack.Sokoban12CostPartition.d589 p)
  have code : read 3999634 = .branch 168 3737620 3737621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode589 p, oldNode591 p]
theorem oldNode593 (p : Pattern) : eval read p 4392024 = NetHack.Sokoban12CostPartition.d593 p := by
  change eval read p 4392024 = (if p 160 then NetHack.Sokoban12CostPartition.d592 p else NetHack.Sokoban12CostPartition.d31 p)
  have code : read 4392024 = .branch 160 3999633 3999634 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode31 p, oldNode592 p]
theorem oldNode594 (p : Pattern) : eval read p 3347243 = NetHack.Sokoban12CostPartition.d594 p := by
  change eval read p 3347243 = (if p 193 then NetHack.Sokoban12CostPartition.d5 p else NetHack.Sokoban12CostPartition.d9 p)
  have code : read 3347243 = .branch 193 1638542 65536 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode9 p, oldNode5 p]
theorem oldNode595 (p : Pattern) : eval read p 3737622 = NetHack.Sokoban12CostPartition.d595 p := by
  change eval read p 3737622 = (if p 186 then NetHack.Sokoban12CostPartition.d594 p else NetHack.Sokoban12CostPartition.d32 p)
  have code : read 3737622 = .branch 186 3347242 3347243 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode32 p, oldNode594 p]
theorem oldNode596 (p : Pattern) : eval read p 3999636 = NetHack.Sokoban12CostPartition.d596 p := by
  change eval read p 3999636 = (if p 168 then NetHack.Sokoban12CostPartition.d595 p else NetHack.Sokoban12CostPartition.d591 p)
  have code : read 3999636 = .branch 168 3737621 3737622 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode591 p, oldNode595 p]
theorem oldNode597 (p : Pattern) : eval read p 4392025 = NetHack.Sokoban12CostPartition.d597 p := by
  change eval read p 4392025 = (if p 160 then NetHack.Sokoban12CostPartition.d596 p else NetHack.Sokoban12CostPartition.d33 p)
  have code : read 4392025 = .branch 160 3999635 3999636 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode33 p, oldNode596 p]
theorem oldNode598 (p : Pattern) : eval read p 4785023 = NetHack.Sokoban12CostPartition.d598 p := by
  change eval read p 4785023 = (if p 141 then NetHack.Sokoban12CostPartition.d597 p else NetHack.Sokoban12CostPartition.d593 p)
  have code : read 4785023 = .branch 141 4392024 4392025 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode593 p, oldNode597 p]
theorem oldNode599 (p : Pattern) : eval read p 3999637 = NetHack.Sokoban12CostPartition.d599 p := by
  change eval read p 3999637 = (if p 168 then NetHack.Sokoban12CostPartition.d590 p else NetHack.Sokoban12CostPartition.d588 p)
  have code : read 3999637 = .branch 168 3411926 3411927 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode588 p, oldNode590 p]
end NetHack.Soko12Forward220.Shared
