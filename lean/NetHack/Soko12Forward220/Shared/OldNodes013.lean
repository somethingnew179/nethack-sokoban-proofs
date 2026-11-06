import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode421 (p : Pattern) : eval read p 4785002 = NetHack.Sokoban12CostPartition.d421 p := by
  change eval read p 4785002 = (if p 141 then NetHack.Sokoban12CostPartition.d420 p else NetHack.Sokoban12CostPartition.d417 p)
  have code : read 4785002 = .branch 141 4523404 4523405 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode417 p, oldNode420 p]
theorem oldNode422 (p : Pattern) : eval read p 4981419 = NetHack.Sokoban12CostPartition.d422 p := by
  change eval read p 4981419 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d421 p)
  have code : read 4981419 = .branch 134 4785002 4785000 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode421 p, oldNode402 p]
theorem oldNode423 (p : Pattern) : eval read p 5046760 = NetHack.Sokoban12CostPartition.d423 p := by
  change eval read p 5046760 = (if p 133 then NetHack.Sokoban12CostPartition.d422 p else NetHack.Sokoban12CostPartition.d414 p)
  have code : read 5046760 = .branch 133 4981418 4981419 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode414 p, oldNode422 p]
theorem oldNode424 (p : Pattern) : eval read p 4523406 = NetHack.Sokoban12CostPartition.d424 p := by
  change eval read p 4523406 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d407 p)
  have code : read 4523406 = .branch 158 4457772 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode407 p, oldNode380 p]
theorem oldNode425 (p : Pattern) : eval read p 4523407 = NetHack.Sokoban12CostPartition.d425 p := by
  change eval read p 4523407 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d411 p)
  have code : read 4523407 = .branch 158 4457773 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode411 p, oldNode386 p]
theorem oldNode426 (p : Pattern) : eval read p 4785003 = NetHack.Sokoban12CostPartition.d426 p := by
  change eval read p 4785003 = (if p 141 then NetHack.Sokoban12CostPartition.d425 p else NetHack.Sokoban12CostPartition.d424 p)
  have code : read 4785003 = .branch 141 4523406 4523407 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode424 p, oldNode425 p]
theorem oldNode427 (p : Pattern) : eval read p 4981420 = NetHack.Sokoban12CostPartition.d427 p := by
  change eval read p 4981420 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d426 p)
  have code : read 4981420 = .branch 134 4785003 4785000 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode426 p, oldNode402 p]
theorem oldNode428 (p : Pattern) : eval read p 5046761 = NetHack.Sokoban12CostPartition.d428 p := by
  change eval read p 5046761 = (if p 133 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d427 p)
  have code : read 5046761 = .branch 133 4981420 4785000 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode427 p, oldNode402 p]
theorem oldNode429 (p : Pattern) : eval read p 5112172 = NetHack.Sokoban12CostPartition.d429 p := by
  change eval read p 5112172 = (if p 132 then NetHack.Sokoban12CostPartition.d428 p else NetHack.Sokoban12CostPartition.d423 p)
  have code : read 5112172 = .branch 132 5046760 5046761 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode423 p, oldNode428 p]
theorem oldNode430 (p : Pattern) : eval read p 5439696 = NetHack.Sokoban12CostPartition.d430 p := by
  change eval read p 5439696 = (if p 108 then NetHack.Sokoban12CostPartition.d429 p else NetHack.Sokoban12CostPartition.d404 p)
  have code : read 5439696 = .branch 108 5112171 5112172 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode404 p, oldNode429 p]
theorem oldNode451 (p : Pattern) : eval read p 4785004 = NetHack.Sokoban12CostPartition.d451 p := by
  change eval read p 4785004 = (if p 141 then NetHack.Sokoban12CostPartition.d62 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4785004 = .branch 141 3737602 3999608 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode62 p]
theorem oldNode452 (p : Pattern) : eval read p 4392006 = NetHack.Sokoban12CostPartition.d452 p := by
  change eval read p 4392006 = (if p 160 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4392006 = .branch 160 3737602 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode55 p]
theorem oldNode453 (p : Pattern) : eval read p 4392007 = NetHack.Sokoban12CostPartition.d453 p := by
  change eval read p 4392007 = (if p 160 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 4392007 = .branch 160 3999608 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode65 p]
theorem oldNode454 (p : Pattern) : eval read p 4785005 = NetHack.Sokoban12CostPartition.d454 p := by
  change eval read p 4785005 = (if p 141 then NetHack.Sokoban12CostPartition.d453 p else NetHack.Sokoban12CostPartition.d452 p)
  have code : read 4785005 = .branch 141 4392006 4392007 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode452 p, oldNode453 p]
theorem oldNode455 (p : Pattern) : eval read p 4981421 = NetHack.Sokoban12CostPartition.d455 p := by
  change eval read p 4981421 = (if p 134 then NetHack.Sokoban12CostPartition.d454 p else NetHack.Sokoban12CostPartition.d451 p)
  have code : read 4981421 = .branch 134 4785004 4785005 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode451 p, oldNode454 p]
theorem oldNode456 (p : Pattern) : eval read p 4523408 = NetHack.Sokoban12CostPartition.d456 p := by
  change eval read p 4523408 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4523408 = .branch 158 3737602 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode55 p]
theorem oldNode457 (p : Pattern) : eval read p 4523409 = NetHack.Sokoban12CostPartition.d457 p := by
  change eval read p 4523409 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 4523409 = .branch 158 3999608 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode65 p]
theorem oldNode458 (p : Pattern) : eval read p 4785006 = NetHack.Sokoban12CostPartition.d458 p := by
  change eval read p 4785006 = (if p 141 then NetHack.Sokoban12CostPartition.d457 p else NetHack.Sokoban12CostPartition.d456 p)
  have code : read 4785006 = .branch 141 4523408 4523409 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode456 p, oldNode457 p]
theorem oldNode459 (p : Pattern) : eval read p 4523410 = NetHack.Sokoban12CostPartition.d459 p := by
  change eval read p 4523410 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d452 p)
  have code : read 4523410 = .branch 158 4392006 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode452 p, oldNode55 p]
theorem oldNode460 (p : Pattern) : eval read p 4523411 = NetHack.Sokoban12CostPartition.d460 p := by
  change eval read p 4523411 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d453 p)
  have code : read 4523411 = .branch 158 4392007 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode453 p, oldNode65 p]
theorem oldNode461 (p : Pattern) : eval read p 4785007 = NetHack.Sokoban12CostPartition.d461 p := by
  change eval read p 4785007 = (if p 141 then NetHack.Sokoban12CostPartition.d460 p else NetHack.Sokoban12CostPartition.d459 p)
  have code : read 4785007 = .branch 141 4523410 4523411 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode459 p, oldNode460 p]
theorem oldNode462 (p : Pattern) : eval read p 4981422 = NetHack.Sokoban12CostPartition.d462 p := by
  change eval read p 4981422 = (if p 134 then NetHack.Sokoban12CostPartition.d461 p else NetHack.Sokoban12CostPartition.d458 p)
  have code : read 4981422 = .branch 134 4785006 4785007 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode458 p, oldNode461 p]
theorem oldNode463 (p : Pattern) : eval read p 5046762 = NetHack.Sokoban12CostPartition.d463 p := by
  change eval read p 5046762 = (if p 133 then NetHack.Sokoban12CostPartition.d462 p else NetHack.Sokoban12CostPartition.d455 p)
  have code : read 5046762 = .branch 133 4981421 4981422 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode455 p, oldNode462 p]
theorem oldNode464 (p : Pattern) : eval read p 5046763 = NetHack.Sokoban12CostPartition.d464 p := by
  change eval read p 5046763 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d462 p)
  have code : read 5046763 = .branch 133 4981422 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode462 p, oldNode66 p]
end NetHack.Soko12Forward220.Shared
