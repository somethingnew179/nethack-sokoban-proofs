import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode63 (p : Pattern) : eval read p 319490 = NetHack.Sokoban12CostPartition.d63 p := by
  change eval read p 319490 = (if p 160 then NetHack.Sokoban12CostPartition.d62 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 319490 = .branch 160 286720 286729 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode62 p]
theorem oldNode64 (p : Pattern) : eval read p 360454 = NetHack.Sokoban12CostPartition.d64 p := by
  change eval read p 360454 = (if p 141 then NetHack.Sokoban12CostPartition.d63 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 360454 = .branch 141 319489 319490 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode63 p]
theorem oldNode65 (p : Pattern) : eval read p 286730 = NetHack.Sokoban12CostPartition.d65 p := by
  change eval read p 286730 = (if p 168 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 286730 = .branch 168 229387 229388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode60 p]
theorem oldNode66 (p : Pattern) : eval read p 360455 = NetHack.Sokoban12CostPartition.d66 p := by
  change eval read p 360455 = (if p 141 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 360455 = .branch 141 229387 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode65 p]
theorem oldNode67 (p : Pattern) : eval read p 368642 = NetHack.Sokoban12CostPartition.d67 p := by
  change eval read p 368642 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 368642 = .branch 134 360454 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode66 p]
theorem oldNode68 (p : Pattern) : eval read p 335873 = NetHack.Sokoban12CostPartition.d68 p := by
  change eval read p 335873 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 335873 = .branch 158 319489 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode55 p]
theorem oldNode69 (p : Pattern) : eval read p 335874 = NetHack.Sokoban12CostPartition.d69 p := by
  change eval read p 335874 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 335874 = .branch 158 319490 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode65 p]
theorem oldNode70 (p : Pattern) : eval read p 360456 = NetHack.Sokoban12CostPartition.d70 p := by
  change eval read p 360456 = (if p 141 then NetHack.Sokoban12CostPartition.d69 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 360456 = .branch 141 335873 335874 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode69 p]
theorem oldNode71 (p : Pattern) : eval read p 368643 = NetHack.Sokoban12CostPartition.d71 p := by
  change eval read p 368643 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 368643 = .branch 134 360456 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode66 p]
theorem oldNode72 (p : Pattern) : eval read p 376834 = NetHack.Sokoban12CostPartition.d72 p := by
  change eval read p 376834 = (if p 133 then NetHack.Sokoban12CostPartition.d71 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 376834 = .branch 133 368642 368643 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode71 p]
theorem oldNode73 (p : Pattern) : eval read p 376835 = NetHack.Sokoban12CostPartition.d73 p := by
  change eval read p 376835 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d71 p)
  have code : read 376835 = .branch 133 368643 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode71 p, oldNode66 p]
theorem oldNode74 (p : Pattern) : eval read p 385025 = NetHack.Sokoban12CostPartition.d74 p := by
  change eval read p 385025 = (if p 132 then NetHack.Sokoban12CostPartition.d73 p else NetHack.Sokoban12CostPartition.d72 p)
  have code : read 385025 = .branch 132 376834 376835 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode72 p, oldNode73 p]
theorem oldNode75 (p : Pattern) : eval read p 409601 = NetHack.Sokoban12CostPartition.d75 p := by
  change eval read p 409601 = (if p 108 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d74 p)
  have code : read 409601 = .branch 108 385025 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode74 p, oldNode66 p]
theorem oldNode106 (p : Pattern) : eval read p 319495 = NetHack.Sokoban12CostPartition.d106 p := by
  change eval read p 319495 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d7 p)
  have code : read 319495 = .branch 160 229376 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode7 p, oldNode55 p]
theorem oldNode107 (p : Pattern) : eval read p 327687 = NetHack.Sokoban12CostPartition.d107 p := by
  change eval read p 327687 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 327687 = .branch 159 319495 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode55 p]
theorem oldNode108 (p : Pattern) : eval read p 335880 = NetHack.Sokoban12CostPartition.d108 p := by
  change eval read p 335880 = (if p 158 then NetHack.Sokoban12CostPartition.d107 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 335880 = .branch 158 319495 327687 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode107 p]
theorem oldNode109 (p : Pattern) : eval read p 319496 = NetHack.Sokoban12CostPartition.d109 p := by
  change eval read p 319496 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 319496 = .branch 160 286720 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode65 p]
theorem oldNode110 (p : Pattern) : eval read p 327688 = NetHack.Sokoban12CostPartition.d110 p := by
  change eval read p 327688 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 327688 = .branch 159 319496 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode65 p]
theorem oldNode111 (p : Pattern) : eval read p 335881 = NetHack.Sokoban12CostPartition.d111 p := by
  change eval read p 335881 = (if p 158 then NetHack.Sokoban12CostPartition.d110 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 335881 = .branch 158 319496 327688 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode110 p]
theorem oldNode112 (p : Pattern) : eval read p 360457 = NetHack.Sokoban12CostPartition.d112 p := by
  change eval read p 360457 = (if p 141 then NetHack.Sokoban12CostPartition.d111 p else NetHack.Sokoban12CostPartition.d108 p)
  have code : read 360457 = .branch 141 335880 335881 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode108 p, oldNode111 p]
theorem oldNode113 (p : Pattern) : eval read p 368648 = NetHack.Sokoban12CostPartition.d113 p := by
  change eval read p 368648 = (if p 134 then NetHack.Sokoban12CostPartition.d112 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 368648 = .branch 134 360454 360457 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode112 p]
theorem oldNode114 (p : Pattern) : eval read p 327689 = NetHack.Sokoban12CostPartition.d114 p := by
  change eval read p 327689 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 327689 = .branch 159 319489 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode55 p]
theorem oldNode115 (p : Pattern) : eval read p 335882 = NetHack.Sokoban12CostPartition.d115 p := by
  change eval read p 335882 = (if p 158 then NetHack.Sokoban12CostPartition.d114 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 335882 = .branch 158 319489 327689 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode114 p]
theorem oldNode116 (p : Pattern) : eval read p 327690 = NetHack.Sokoban12CostPartition.d116 p := by
  change eval read p 327690 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 327690 = .branch 159 319490 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode65 p]
end NetHack.Soko12Forward219.Shared
