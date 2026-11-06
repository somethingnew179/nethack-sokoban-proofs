import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode672 (p : Pattern) : eval read p 4392035 = NetHack.Sokoban12CostPartition.d672 p := by
  change eval read p 4392035 = (if p 160 then NetHack.Sokoban12CostPartition.d671 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 4392035 = .branch 160 3999645 3999646 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode671 p]
theorem oldNode673 (p : Pattern) : eval read p 4785031 = NetHack.Sokoban12CostPartition.d673 p := by
  change eval read p 4785031 = (if p 141 then NetHack.Sokoban12CostPartition.d672 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 4785031 = .branch 141 4392034 4392035 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode672 p]
theorem oldNode674 (p : Pattern) : eval read p 3999647 = NetHack.Sokoban12CostPartition.d674 p := by
  change eval read p 3999647 = (if p 168 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d662 p)
  have code : read 3999647 = .branch 168 3411930 3411931 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode662 p, oldNode665 p]
theorem oldNode675 (p : Pattern) : eval read p 4392036 = NetHack.Sokoban12CostPartition.d675 p := by
  change eval read p 4392036 = (if p 160 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 4392036 = .branch 160 3999643 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode674 p]
theorem oldNode676 (p : Pattern) : eval read p 3671975 = NetHack.Sokoban12CostPartition.d676 p := by
  change eval read p 3671975 = (if p 187 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 3671975 = .branch 187 3411928 3411930 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode662 p]
theorem oldNode677 (p : Pattern) : eval read p 3737632 = NetHack.Sokoban12CostPartition.d677 p := by
  change eval read p 3737632 = (if p 186 then NetHack.Sokoban12CostPartition.d676 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 3737632 = .branch 186 3411928 3671975 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode676 p]
theorem oldNode678 (p : Pattern) : eval read p 3671976 = NetHack.Sokoban12CostPartition.d678 p := by
  change eval read p 3671976 = (if p 187 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 3671976 = .branch 187 3411929 3411931 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode665 p]
theorem oldNode679 (p : Pattern) : eval read p 3737633 = NetHack.Sokoban12CostPartition.d679 p := by
  change eval read p 3737633 = (if p 186 then NetHack.Sokoban12CostPartition.d678 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 3737633 = .branch 186 3411929 3671976 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode678 p]
theorem oldNode680 (p : Pattern) : eval read p 3999648 = NetHack.Sokoban12CostPartition.d680 p := by
  change eval read p 3999648 = (if p 168 then NetHack.Sokoban12CostPartition.d679 p else NetHack.Sokoban12CostPartition.d677 p)
  have code : read 3999648 = .branch 168 3737632 3737633 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode677 p, oldNode679 p]
theorem oldNode681 (p : Pattern) : eval read p 4392037 = NetHack.Sokoban12CostPartition.d681 p := by
  change eval read p 4392037 = (if p 160 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d680 p)
  have code : read 4392037 = .branch 160 3999648 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode680 p, oldNode674 p]
theorem oldNode682 (p : Pattern) : eval read p 4457790 = NetHack.Sokoban12CostPartition.d682 p := by
  change eval read p 4457790 = (if p 159 then NetHack.Sokoban12CostPartition.d681 p else NetHack.Sokoban12CostPartition.d675 p)
  have code : read 4457790 = .branch 159 4392036 4392037 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode675 p, oldNode681 p]
theorem oldNode683 (p : Pattern) : eval read p 4523446 = NetHack.Sokoban12CostPartition.d683 p := by
  change eval read p 4523446 = (if p 158 then NetHack.Sokoban12CostPartition.d682 p else NetHack.Sokoban12CostPartition.d675 p)
  have code : read 4523446 = .branch 158 4392036 4457790 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode675 p, oldNode682 p]
theorem oldNode684 (p : Pattern) : eval read p 3999649 = NetHack.Sokoban12CostPartition.d684 p := by
  change eval read p 3999649 = (if p 168 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d665 p)
  have code : read 3999649 = .branch 168 3411931 3411933 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode665 p, oldNode669 p]
theorem oldNode685 (p : Pattern) : eval read p 4392038 = NetHack.Sokoban12CostPartition.d685 p := by
  change eval read p 4392038 = (if p 160 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 4392038 = .branch 160 3999645 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode684 p]
theorem oldNode686 (p : Pattern) : eval read p 3671977 = NetHack.Sokoban12CostPartition.d686 p := by
  change eval read p 3671977 = (if p 187 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 3671977 = .branch 187 3411932 3411933 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode669 p]
theorem oldNode687 (p : Pattern) : eval read p 3737634 = NetHack.Sokoban12CostPartition.d687 p := by
  change eval read p 3737634 = (if p 186 then NetHack.Sokoban12CostPartition.d686 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 3737634 = .branch 186 3411932 3671977 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode686 p]
theorem oldNode688 (p : Pattern) : eval read p 3999650 = NetHack.Sokoban12CostPartition.d688 p := by
  change eval read p 3999650 = (if p 168 then NetHack.Sokoban12CostPartition.d687 p else NetHack.Sokoban12CostPartition.d679 p)
  have code : read 3999650 = .branch 168 3737633 3737634 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode679 p, oldNode687 p]
theorem oldNode689 (p : Pattern) : eval read p 4392039 = NetHack.Sokoban12CostPartition.d689 p := by
  change eval read p 4392039 = (if p 160 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d688 p)
  have code : read 4392039 = .branch 160 3999650 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode688 p, oldNode684 p]
theorem oldNode690 (p : Pattern) : eval read p 4457791 = NetHack.Sokoban12CostPartition.d690 p := by
  change eval read p 4457791 = (if p 159 then NetHack.Sokoban12CostPartition.d689 p else NetHack.Sokoban12CostPartition.d685 p)
  have code : read 4457791 = .branch 159 4392038 4392039 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode685 p, oldNode689 p]
theorem oldNode691 (p : Pattern) : eval read p 4523447 = NetHack.Sokoban12CostPartition.d691 p := by
  change eval read p 4523447 = (if p 158 then NetHack.Sokoban12CostPartition.d690 p else NetHack.Sokoban12CostPartition.d685 p)
  have code : read 4523447 = .branch 158 4392038 4457791 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode685 p, oldNode690 p]
theorem oldNode692 (p : Pattern) : eval read p 4785032 = NetHack.Sokoban12CostPartition.d692 p := by
  change eval read p 4785032 = (if p 141 then NetHack.Sokoban12CostPartition.d691 p else NetHack.Sokoban12CostPartition.d683 p)
  have code : read 4785032 = .branch 141 4523446 4523447 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode683 p, oldNode691 p]
theorem oldNode693 (p : Pattern) : eval read p 4981440 = NetHack.Sokoban12CostPartition.d693 p := by
  change eval read p 4981440 = (if p 134 then NetHack.Sokoban12CostPartition.d692 p else NetHack.Sokoban12CostPartition.d673 p)
  have code : read 4981440 = .branch 134 4785031 4785032 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode673 p, oldNode692 p]
theorem oldNode694 (p : Pattern) : eval read p 4523448 = NetHack.Sokoban12CostPartition.d694 p := by
  change eval read p 4523448 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 4523448 = .branch 158 4392034 3999647 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode674 p]
theorem oldNode695 (p : Pattern) : eval read p 4523449 = NetHack.Sokoban12CostPartition.d695 p := by
  change eval read p 4523449 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 4523449 = .branch 158 4392035 3999649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode684 p]
end NetHack.Soko12Forward220.Shared
