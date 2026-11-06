import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode117 (p : Pattern) : eval read p 335883 = NetHack.Sokoban12CostPartition.d117 p := by
  change eval read p 335883 = (if p 158 then NetHack.Sokoban12CostPartition.d116 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 335883 = .branch 158 319490 327690 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode116 p]
theorem oldNode118 (p : Pattern) : eval read p 360458 = NetHack.Sokoban12CostPartition.d118 p := by
  change eval read p 360458 = (if p 141 then NetHack.Sokoban12CostPartition.d117 p else NetHack.Sokoban12CostPartition.d115 p)
  have code : read 360458 = .branch 141 335882 335883 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode115 p, oldNode117 p]
theorem oldNode119 (p : Pattern) : eval read p 262145 = NetHack.Sokoban12CostPartition.d119 p := by
  change eval read p 262145 = (if p 187 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 262145 = .branch 187 229376 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode120 (p : Pattern) : eval read p 270341 = NetHack.Sokoban12CostPartition.d120 p := by
  change eval read p 270341 = (if p 186 then NetHack.Sokoban12CostPartition.d119 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 270341 = .branch 186 229376 262145 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode119 p]
theorem oldNode121 (p : Pattern) : eval read p 319497 = NetHack.Sokoban12CostPartition.d121 p := by
  change eval read p 319497 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 319497 = .branch 160 270341 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode55 p]
theorem oldNode122 (p : Pattern) : eval read p 327691 = NetHack.Sokoban12CostPartition.d122 p := by
  change eval read p 327691 = (if p 159 then NetHack.Sokoban12CostPartition.d121 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 327691 = .branch 159 319495 319497 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode121 p]
theorem oldNode123 (p : Pattern) : eval read p 327692 = NetHack.Sokoban12CostPartition.d123 p := by
  change eval read p 327692 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d121 p)
  have code : read 327692 = .branch 159 319497 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode121 p, oldNode55 p]
theorem oldNode124 (p : Pattern) : eval read p 335884 = NetHack.Sokoban12CostPartition.d124 p := by
  change eval read p 335884 = (if p 158 then NetHack.Sokoban12CostPartition.d123 p else NetHack.Sokoban12CostPartition.d122 p)
  have code : read 335884 = .branch 158 327691 327692 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode122 p, oldNode123 p]
theorem oldNode125 (p : Pattern) : eval read p 262146 = NetHack.Sokoban12CostPartition.d125 p := by
  change eval read p 262146 = (if p 187 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 262146 = .branch 187 229377 229388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode60 p]
theorem oldNode126 (p : Pattern) : eval read p 270342 = NetHack.Sokoban12CostPartition.d126 p := by
  change eval read p 270342 = (if p 186 then NetHack.Sokoban12CostPartition.d125 p else NetHack.Sokoban12CostPartition.d11 p)
  have code : read 270342 = .branch 186 229377 262146 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode11 p, oldNode125 p]
theorem oldNode127 (p : Pattern) : eval read p 286731 = NetHack.Sokoban12CostPartition.d127 p := by
  change eval read p 286731 = (if p 168 then NetHack.Sokoban12CostPartition.d126 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 286731 = .branch 168 270341 270342 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode126 p]
theorem oldNode128 (p : Pattern) : eval read p 319498 = NetHack.Sokoban12CostPartition.d128 p := by
  change eval read p 319498 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d127 p)
  have code : read 319498 = .branch 160 286731 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode127 p, oldNode65 p]
theorem oldNode129 (p : Pattern) : eval read p 327693 = NetHack.Sokoban12CostPartition.d129 p := by
  change eval read p 327693 = (if p 159 then NetHack.Sokoban12CostPartition.d128 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 327693 = .branch 159 319496 319498 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode128 p]
theorem oldNode130 (p : Pattern) : eval read p 327694 = NetHack.Sokoban12CostPartition.d130 p := by
  change eval read p 327694 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d128 p)
  have code : read 327694 = .branch 159 319498 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode128 p, oldNode65 p]
theorem oldNode131 (p : Pattern) : eval read p 335885 = NetHack.Sokoban12CostPartition.d131 p := by
  change eval read p 335885 = (if p 158 then NetHack.Sokoban12CostPartition.d130 p else NetHack.Sokoban12CostPartition.d129 p)
  have code : read 335885 = .branch 158 327693 327694 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode129 p, oldNode130 p]
theorem oldNode132 (p : Pattern) : eval read p 360459 = NetHack.Sokoban12CostPartition.d132 p := by
  change eval read p 360459 = (if p 141 then NetHack.Sokoban12CostPartition.d131 p else NetHack.Sokoban12CostPartition.d124 p)
  have code : read 360459 = .branch 141 335884 335885 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode124 p, oldNode131 p]
theorem oldNode133 (p : Pattern) : eval read p 368649 = NetHack.Sokoban12CostPartition.d133 p := by
  change eval read p 368649 = (if p 134 then NetHack.Sokoban12CostPartition.d132 p else NetHack.Sokoban12CostPartition.d118 p)
  have code : read 368649 = .branch 134 360458 360459 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode118 p, oldNode132 p]
theorem oldNode134 (p : Pattern) : eval read p 376840 = NetHack.Sokoban12CostPartition.d134 p := by
  change eval read p 376840 = (if p 133 then NetHack.Sokoban12CostPartition.d133 p else NetHack.Sokoban12CostPartition.d113 p)
  have code : read 376840 = .branch 133 368648 368649 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode113 p, oldNode133 p]
theorem oldNode135 (p : Pattern) : eval read p 376841 = NetHack.Sokoban12CostPartition.d135 p := by
  change eval read p 376841 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d133 p)
  have code : read 376841 = .branch 133 368649 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode133 p, oldNode66 p]
theorem oldNode136 (p : Pattern) : eval read p 385028 = NetHack.Sokoban12CostPartition.d136 p := by
  change eval read p 385028 = (if p 132 then NetHack.Sokoban12CostPartition.d135 p else NetHack.Sokoban12CostPartition.d134 p)
  have code : read 385028 = .branch 132 376840 376841 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode134 p, oldNode135 p]
theorem oldNode137 (p : Pattern) : eval read p 270343 = NetHack.Sokoban12CostPartition.d137 p := by
  change eval read p 270343 = (if p 186 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 270343 = .branch 186 262145 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode55 p]
theorem oldNode138 (p : Pattern) : eval read p 319499 = NetHack.Sokoban12CostPartition.d138 p := by
  change eval read p 319499 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 319499 = .branch 160 229376 270343 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode137 p]
theorem oldNode139 (p : Pattern) : eval read p 319500 = NetHack.Sokoban12CostPartition.d139 p := by
  change eval read p 319500 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 319500 = .branch 160 270341 270343 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode137 p]
theorem oldNode140 (p : Pattern) : eval read p 327695 = NetHack.Sokoban12CostPartition.d140 p := by
  change eval read p 327695 = (if p 159 then NetHack.Sokoban12CostPartition.d139 p else NetHack.Sokoban12CostPartition.d138 p)
  have code : read 327695 = .branch 159 319499 319500 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode138 p, oldNode139 p]
end NetHack.Soko12Forward219.Shared
