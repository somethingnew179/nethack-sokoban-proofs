import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode465 (p : Pattern) : eval read p 385064 = NetHack.Sokoban12CostPartition.d465 p := by
  change eval read p 385064 = (if p 132 then NetHack.Sokoban12CostPartition.d464 p else NetHack.Sokoban12CostPartition.d463 p)
  have code : read 385064 = .branch 132 376898 376899 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode463 p, oldNode464 p]
theorem oldNode466 (p : Pattern) : eval read p 319522 = NetHack.Sokoban12CostPartition.d466 p := by
  change eval read p 319522 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 319522 = .branch 160 270337 270343 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode137 p]
theorem oldNode467 (p : Pattern) : eval read p 327714 = NetHack.Sokoban12CostPartition.d467 p := by
  change eval read p 327714 = (if p 159 then NetHack.Sokoban12CostPartition.d466 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 327714 = .branch 159 270337 319522 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode466 p]
theorem oldNode468 (p : Pattern) : eval read p 335944 = NetHack.Sokoban12CostPartition.d468 p := by
  change eval read p 335944 = (if p 158 then NetHack.Sokoban12CostPartition.d467 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 335944 = .branch 158 270337 327714 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode467 p]
theorem oldNode469 (p : Pattern) : eval read p 319523 = NetHack.Sokoban12CostPartition.d469 p := by
  change eval read p 319523 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 319523 = .branch 160 286729 286732 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode144 p]
theorem oldNode470 (p : Pattern) : eval read p 327715 = NetHack.Sokoban12CostPartition.d470 p := by
  change eval read p 327715 = (if p 159 then NetHack.Sokoban12CostPartition.d469 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 327715 = .branch 159 286729 319523 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode469 p]
theorem oldNode471 (p : Pattern) : eval read p 335945 = NetHack.Sokoban12CostPartition.d471 p := by
  change eval read p 335945 = (if p 158 then NetHack.Sokoban12CostPartition.d470 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 335945 = .branch 158 286729 327715 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode470 p]
theorem oldNode472 (p : Pattern) : eval read p 360494 = NetHack.Sokoban12CostPartition.d472 p := by
  change eval read p 360494 = (if p 141 then NetHack.Sokoban12CostPartition.d471 p else NetHack.Sokoban12CostPartition.d468 p)
  have code : read 360494 = .branch 141 335944 335945 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode468 p, oldNode471 p]
theorem oldNode473 (p : Pattern) : eval read p 368704 = NetHack.Sokoban12CostPartition.d473 p := by
  change eval read p 368704 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d472 p)
  have code : read 368704 = .branch 134 360494 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode472 p, oldNode66 p]
theorem oldNode474 (p : Pattern) : eval read p 335946 = NetHack.Sokoban12CostPartition.d474 p := by
  change eval read p 335946 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d466 p)
  have code : read 335946 = .branch 158 319522 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode466 p, oldNode55 p]
theorem oldNode475 (p : Pattern) : eval read p 335947 = NetHack.Sokoban12CostPartition.d475 p := by
  change eval read p 335947 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d469 p)
  have code : read 335947 = .branch 158 319523 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode469 p, oldNode65 p]
theorem oldNode476 (p : Pattern) : eval read p 360495 = NetHack.Sokoban12CostPartition.d476 p := by
  change eval read p 360495 = (if p 141 then NetHack.Sokoban12CostPartition.d475 p else NetHack.Sokoban12CostPartition.d474 p)
  have code : read 360495 = .branch 141 335946 335947 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode474 p, oldNode475 p]
theorem oldNode477 (p : Pattern) : eval read p 368705 = NetHack.Sokoban12CostPartition.d477 p := by
  change eval read p 368705 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d476 p)
  have code : read 368705 = .branch 134 360495 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode476 p, oldNode66 p]
theorem oldNode478 (p : Pattern) : eval read p 376900 = NetHack.Sokoban12CostPartition.d478 p := by
  change eval read p 376900 = (if p 133 then NetHack.Sokoban12CostPartition.d477 p else NetHack.Sokoban12CostPartition.d473 p)
  have code : read 376900 = .branch 133 368704 368705 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode473 p, oldNode477 p]
theorem oldNode479 (p : Pattern) : eval read p 335948 = NetHack.Sokoban12CostPartition.d479 p := by
  change eval read p 335948 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d467 p)
  have code : read 335948 = .branch 158 327714 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode467 p, oldNode55 p]
theorem oldNode480 (p : Pattern) : eval read p 335949 = NetHack.Sokoban12CostPartition.d480 p := by
  change eval read p 335949 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d470 p)
  have code : read 335949 = .branch 158 327715 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode470 p, oldNode65 p]
theorem oldNode481 (p : Pattern) : eval read p 360496 = NetHack.Sokoban12CostPartition.d481 p := by
  change eval read p 360496 = (if p 141 then NetHack.Sokoban12CostPartition.d480 p else NetHack.Sokoban12CostPartition.d479 p)
  have code : read 360496 = .branch 141 335948 335949 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode479 p, oldNode480 p]
theorem oldNode482 (p : Pattern) : eval read p 368706 = NetHack.Sokoban12CostPartition.d482 p := by
  change eval read p 368706 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d481 p)
  have code : read 368706 = .branch 134 360496 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode481 p, oldNode66 p]
theorem oldNode483 (p : Pattern) : eval read p 376901 = NetHack.Sokoban12CostPartition.d483 p := by
  change eval read p 376901 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d482 p)
  have code : read 376901 = .branch 133 368706 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode482 p, oldNode66 p]
theorem oldNode484 (p : Pattern) : eval read p 385065 = NetHack.Sokoban12CostPartition.d484 p := by
  change eval read p 385065 = (if p 132 then NetHack.Sokoban12CostPartition.d483 p else NetHack.Sokoban12CostPartition.d478 p)
  have code : read 385065 = .branch 132 376900 376901 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode478 p, oldNode483 p]
theorem oldNode485 (p : Pattern) : eval read p 409622 = NetHack.Sokoban12CostPartition.d485 p := by
  change eval read p 409622 = (if p 108 then NetHack.Sokoban12CostPartition.d484 p else NetHack.Sokoban12CostPartition.d465 p)
  have code : read 409622 = .branch 108 385064 385065 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode465 p, oldNode484 p]
theorem oldNode501 (p : Pattern) : eval read p 319526 = NetHack.Sokoban12CostPartition.d501 p := by
  change eval read p 319526 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 319526 = .branch 160 262145 270343 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode137 p]
theorem oldNode502 (p : Pattern) : eval read p 286745 = NetHack.Sokoban12CostPartition.d502 p := by
  change eval read p 286745 = (if p 168 then NetHack.Sokoban12CostPartition.d125 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 286745 = .branch 168 262145 262146 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode125 p]
theorem oldNode503 (p : Pattern) : eval read p 319527 = NetHack.Sokoban12CostPartition.d503 p := by
  change eval read p 319527 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d502 p)
  have code : read 319527 = .branch 160 286745 286732 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode502 p, oldNode144 p]
end NetHack.Soko12Forward219.Shared
