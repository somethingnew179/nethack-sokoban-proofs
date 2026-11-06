import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode421 (p : Pattern) : eval read p 360488 = NetHack.Sokoban12CostPartition.d421 p := by
  change eval read p 360488 = (if p 141 then NetHack.Sokoban12CostPartition.d420 p else NetHack.Sokoban12CostPartition.d417 p)
  have code : read 360488 = .branch 141 335931 335932 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode417 p, oldNode420 p]
theorem oldNode422 (p : Pattern) : eval read p 368695 = NetHack.Sokoban12CostPartition.d422 p := by
  change eval read p 368695 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d421 p)
  have code : read 368695 = .branch 134 360488 360486 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode421 p, oldNode402 p]
theorem oldNode423 (p : Pattern) : eval read p 376892 = NetHack.Sokoban12CostPartition.d423 p := by
  change eval read p 376892 = (if p 133 then NetHack.Sokoban12CostPartition.d422 p else NetHack.Sokoban12CostPartition.d414 p)
  have code : read 376892 = .branch 133 368694 368695 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode414 p, oldNode422 p]
theorem oldNode424 (p : Pattern) : eval read p 335933 = NetHack.Sokoban12CostPartition.d424 p := by
  change eval read p 335933 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d407 p)
  have code : read 335933 = .branch 158 327709 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode407 p, oldNode380 p]
theorem oldNode425 (p : Pattern) : eval read p 335934 = NetHack.Sokoban12CostPartition.d425 p := by
  change eval read p 335934 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d411 p)
  have code : read 335934 = .branch 158 327710 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode411 p, oldNode386 p]
theorem oldNode426 (p : Pattern) : eval read p 360489 = NetHack.Sokoban12CostPartition.d426 p := by
  change eval read p 360489 = (if p 141 then NetHack.Sokoban12CostPartition.d425 p else NetHack.Sokoban12CostPartition.d424 p)
  have code : read 360489 = .branch 141 335933 335934 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode424 p, oldNode425 p]
theorem oldNode427 (p : Pattern) : eval read p 368696 = NetHack.Sokoban12CostPartition.d427 p := by
  change eval read p 368696 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d426 p)
  have code : read 368696 = .branch 134 360489 360486 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode426 p, oldNode402 p]
theorem oldNode428 (p : Pattern) : eval read p 376893 = NetHack.Sokoban12CostPartition.d428 p := by
  change eval read p 376893 = (if p 133 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d427 p)
  have code : read 376893 = .branch 133 368696 360486 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode427 p, oldNode402 p]
theorem oldNode429 (p : Pattern) : eval read p 385061 = NetHack.Sokoban12CostPartition.d429 p := by
  change eval read p 385061 = (if p 132 then NetHack.Sokoban12CostPartition.d428 p else NetHack.Sokoban12CostPartition.d423 p)
  have code : read 385061 = .branch 132 376892 376893 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode423 p, oldNode428 p]
theorem oldNode430 (p : Pattern) : eval read p 409620 = NetHack.Sokoban12CostPartition.d430 p := by
  change eval read p 409620 = (if p 108 then NetHack.Sokoban12CostPartition.d429 p else NetHack.Sokoban12CostPartition.d404 p)
  have code : read 409620 = .branch 108 385060 385061 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode404 p, oldNode429 p]
theorem oldNode451 (p : Pattern) : eval read p 360490 = NetHack.Sokoban12CostPartition.d451 p := by
  change eval read p 360490 = (if p 141 then NetHack.Sokoban12CostPartition.d62 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 360490 = .branch 141 270337 286729 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode62 p]
theorem oldNode452 (p : Pattern) : eval read p 319520 = NetHack.Sokoban12CostPartition.d452 p := by
  change eval read p 319520 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 319520 = .branch 160 270337 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode55 p]
theorem oldNode453 (p : Pattern) : eval read p 319521 = NetHack.Sokoban12CostPartition.d453 p := by
  change eval read p 319521 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 319521 = .branch 160 286729 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode65 p]
theorem oldNode454 (p : Pattern) : eval read p 360491 = NetHack.Sokoban12CostPartition.d454 p := by
  change eval read p 360491 = (if p 141 then NetHack.Sokoban12CostPartition.d453 p else NetHack.Sokoban12CostPartition.d452 p)
  have code : read 360491 = .branch 141 319520 319521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode452 p, oldNode453 p]
theorem oldNode455 (p : Pattern) : eval read p 368702 = NetHack.Sokoban12CostPartition.d455 p := by
  change eval read p 368702 = (if p 134 then NetHack.Sokoban12CostPartition.d454 p else NetHack.Sokoban12CostPartition.d451 p)
  have code : read 368702 = .branch 134 360490 360491 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode451 p, oldNode454 p]
theorem oldNode456 (p : Pattern) : eval read p 335940 = NetHack.Sokoban12CostPartition.d456 p := by
  change eval read p 335940 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 335940 = .branch 158 270337 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode55 p]
theorem oldNode457 (p : Pattern) : eval read p 335941 = NetHack.Sokoban12CostPartition.d457 p := by
  change eval read p 335941 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 335941 = .branch 158 286729 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode65 p]
theorem oldNode458 (p : Pattern) : eval read p 360492 = NetHack.Sokoban12CostPartition.d458 p := by
  change eval read p 360492 = (if p 141 then NetHack.Sokoban12CostPartition.d457 p else NetHack.Sokoban12CostPartition.d456 p)
  have code : read 360492 = .branch 141 335940 335941 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode456 p, oldNode457 p]
theorem oldNode459 (p : Pattern) : eval read p 335942 = NetHack.Sokoban12CostPartition.d459 p := by
  change eval read p 335942 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d452 p)
  have code : read 335942 = .branch 158 319520 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode452 p, oldNode55 p]
theorem oldNode460 (p : Pattern) : eval read p 335943 = NetHack.Sokoban12CostPartition.d460 p := by
  change eval read p 335943 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d453 p)
  have code : read 335943 = .branch 158 319521 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode453 p, oldNode65 p]
theorem oldNode461 (p : Pattern) : eval read p 360493 = NetHack.Sokoban12CostPartition.d461 p := by
  change eval read p 360493 = (if p 141 then NetHack.Sokoban12CostPartition.d460 p else NetHack.Sokoban12CostPartition.d459 p)
  have code : read 360493 = .branch 141 335942 335943 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode459 p, oldNode460 p]
theorem oldNode462 (p : Pattern) : eval read p 368703 = NetHack.Sokoban12CostPartition.d462 p := by
  change eval read p 368703 = (if p 134 then NetHack.Sokoban12CostPartition.d461 p else NetHack.Sokoban12CostPartition.d458 p)
  have code : read 368703 = .branch 134 360492 360493 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode458 p, oldNode461 p]
theorem oldNode463 (p : Pattern) : eval read p 376898 = NetHack.Sokoban12CostPartition.d463 p := by
  change eval read p 376898 = (if p 133 then NetHack.Sokoban12CostPartition.d462 p else NetHack.Sokoban12CostPartition.d455 p)
  have code : read 376898 = .branch 133 368702 368703 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode455 p, oldNode462 p]
theorem oldNode464 (p : Pattern) : eval read p 376899 = NetHack.Sokoban12CostPartition.d464 p := by
  change eval read p 376899 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d462 p)
  have code : read 376899 = .branch 133 368703 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode462 p, oldNode66 p]
end NetHack.Soko12Forward219.Shared
