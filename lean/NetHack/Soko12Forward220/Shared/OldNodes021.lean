import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode648 (p : Pattern) : eval read p 4523443 = NetHack.Sokoban12CostPartition.d648 p := by
  change eval read p 4523443 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d647 p)
  have code : read 4523443 = .branch 158 4457789 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode647 p, oldNode609 p]
theorem oldNode649 (p : Pattern) : eval read p 4785029 = NetHack.Sokoban12CostPartition.d649 p := by
  change eval read p 4785029 = (if p 141 then NetHack.Sokoban12CostPartition.d648 p else NetHack.Sokoban12CostPartition.d645 p)
  have code : read 4785029 = .branch 141 4523442 4523443 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode645 p, oldNode648 p]
theorem oldNode650 (p : Pattern) : eval read p 4981438 = NetHack.Sokoban12CostPartition.d650 p := by
  change eval read p 4981438 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d649 p)
  have code : read 4981438 = .branch 134 4785029 4785027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode649 p, oldNode627 p]
theorem oldNode651 (p : Pattern) : eval read p 5046776 = NetHack.Sokoban12CostPartition.d651 p := by
  change eval read p 5046776 = (if p 133 then NetHack.Sokoban12CostPartition.d650 p else NetHack.Sokoban12CostPartition.d642 p)
  have code : read 5046776 = .branch 133 4981437 4981438 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode642 p, oldNode650 p]
theorem oldNode652 (p : Pattern) : eval read p 4523444 = NetHack.Sokoban12CostPartition.d652 p := by
  change eval read p 4523444 = (if p 158 then NetHack.Sokoban12CostPartition.d599 p else NetHack.Sokoban12CostPartition.d634 p)
  have code : read 4523444 = .branch 158 4457786 3999637 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode634 p, oldNode599 p]
theorem oldNode653 (p : Pattern) : eval read p 4523445 = NetHack.Sokoban12CostPartition.d653 p := by
  change eval read p 4523445 = (if p 158 then NetHack.Sokoban12CostPartition.d609 p else NetHack.Sokoban12CostPartition.d639 p)
  have code : read 4523445 = .branch 158 4457787 3999639 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode639 p, oldNode609 p]
theorem oldNode654 (p : Pattern) : eval read p 4785030 = NetHack.Sokoban12CostPartition.d654 p := by
  change eval read p 4785030 = (if p 141 then NetHack.Sokoban12CostPartition.d653 p else NetHack.Sokoban12CostPartition.d652 p)
  have code : read 4785030 = .branch 141 4523444 4523445 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode652 p, oldNode653 p]
theorem oldNode655 (p : Pattern) : eval read p 4981439 = NetHack.Sokoban12CostPartition.d655 p := by
  change eval read p 4981439 = (if p 134 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d654 p)
  have code : read 4981439 = .branch 134 4785030 4785027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode654 p, oldNode627 p]
theorem oldNode656 (p : Pattern) : eval read p 5046777 = NetHack.Sokoban12CostPartition.d656 p := by
  change eval read p 5046777 = (if p 133 then NetHack.Sokoban12CostPartition.d627 p else NetHack.Sokoban12CostPartition.d655 p)
  have code : read 5046777 = .branch 133 4981439 4785027 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode655 p, oldNode627 p]
theorem oldNode657 (p : Pattern) : eval read p 5112180 = NetHack.Sokoban12CostPartition.d657 p := by
  change eval read p 5112180 = (if p 132 then NetHack.Sokoban12CostPartition.d656 p else NetHack.Sokoban12CostPartition.d651 p)
  have code : read 5112180 = .branch 132 5046776 5046777 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode651 p, oldNode656 p]
theorem oldNode658 (p : Pattern) : eval read p 5439700 = NetHack.Sokoban12CostPartition.d658 p := by
  change eval read p 5439700 = (if p 108 then NetHack.Sokoban12CostPartition.d657 p else NetHack.Sokoban12CostPartition.d629 p)
  have code : read 5439700 = .branch 108 5112179 5112180 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode629 p, oldNode657 p]
theorem oldNode659 (p : Pattern) : eval read p 1638547 = NetHack.Sokoban12CostPartition.d659 p := by
  change eval read p 1638547 = (if p 271 then NetHack.Sokoban12CostPartition.d4 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 1638547 = .branch 271 2 4 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode4 p]
theorem oldNode660 (p : Pattern) : eval read p 3347247 = NetHack.Sokoban12CostPartition.d660 p := by
  change eval read p 3347247 = (if p 193 then NetHack.Sokoban12CostPartition.d659 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3347247 = .branch 193 2 1638547 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode659 p]
theorem oldNode661 (p : Pattern) : eval read p 3347248 = NetHack.Sokoban12CostPartition.d661 p := by
  change eval read p 3347248 = (if p 193 then NetHack.Sokoban12CostPartition.d58 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 3347248 = .branch 193 1638545 1638543 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode58 p]
theorem oldNode662 (p : Pattern) : eval read p 3411930 = NetHack.Sokoban12CostPartition.d662 p := by
  change eval read p 3411930 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d660 p)
  have code : read 3411930 = .branch 192 3347247 3347248 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode660 p, oldNode661 p]
theorem oldNode663 (p : Pattern) : eval read p 3737629 = NetHack.Sokoban12CostPartition.d663 p := by
  change eval read p 3737629 = (if p 186 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 3737629 = .branch 186 3411928 3411930 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode662 p]
theorem oldNode664 (p : Pattern) : eval read p 3347249 = NetHack.Sokoban12CostPartition.d664 p := by
  change eval read p 3347249 = (if p 193 then NetHack.Sokoban12CostPartition.d262 p else NetHack.Sokoban12CostPartition.d2 p)
  have code : read 3347249 = .branch 193 2 1638545 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode2 p, oldNode262 p]
theorem oldNode665 (p : Pattern) : eval read p 3411931 = NetHack.Sokoban12CostPartition.d665 p := by
  change eval read p 3411931 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d664 p)
  have code : read 3411931 = .branch 192 3347249 3347248 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode664 p, oldNode661 p]
theorem oldNode666 (p : Pattern) : eval read p 3737630 = NetHack.Sokoban12CostPartition.d666 p := by
  change eval read p 3737630 = (if p 186 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 3737630 = .branch 186 3411929 3411931 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode665 p]
theorem oldNode667 (p : Pattern) : eval read p 3999644 = NetHack.Sokoban12CostPartition.d667 p := by
  change eval read p 3999644 = (if p 168 then NetHack.Sokoban12CostPartition.d666 p else NetHack.Sokoban12CostPartition.d663 p)
  have code : read 3999644 = .branch 168 3737629 3737630 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode663 p, oldNode666 p]
theorem oldNode668 (p : Pattern) : eval read p 4392034 = NetHack.Sokoban12CostPartition.d668 p := by
  change eval read p 4392034 = (if p 160 then NetHack.Sokoban12CostPartition.d667 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 4392034 = .branch 160 3999643 3999644 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode667 p]
theorem oldNode669 (p : Pattern) : eval read p 3411933 = NetHack.Sokoban12CostPartition.d669 p := by
  change eval read p 3411933 = (if p 192 then NetHack.Sokoban12CostPartition.d661 p else NetHack.Sokoban12CostPartition.d262 p)
  have code : read 3411933 = .branch 192 1638545 3347248 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode262 p, oldNode661 p]
theorem oldNode670 (p : Pattern) : eval read p 3737631 = NetHack.Sokoban12CostPartition.d670 p := by
  change eval read p 3737631 = (if p 186 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 3737631 = .branch 186 3411932 3411933 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode669 p]
theorem oldNode671 (p : Pattern) : eval read p 3999646 = NetHack.Sokoban12CostPartition.d671 p := by
  change eval read p 3999646 = (if p 168 then NetHack.Sokoban12CostPartition.d670 p else NetHack.Sokoban12CostPartition.d666 p)
  have code : read 3999646 = .branch 168 3737630 3737631 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode666 p, oldNode670 p]
end NetHack.Soko12Forward220.Shared
