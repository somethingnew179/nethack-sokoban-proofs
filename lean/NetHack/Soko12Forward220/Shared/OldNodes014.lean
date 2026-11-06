import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode465 (p : Pattern) : eval read p 5112173 = NetHack.Sokoban12CostPartition.d465 p := by
  change eval read p 5112173 = (if p 132 then NetHack.Sokoban12CostPartition.d464 p else NetHack.Sokoban12CostPartition.d463 p)
  have code : read 5112173 = .branch 132 5046762 5046763 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode463 p, oldNode464 p]
theorem oldNode466 (p : Pattern) : eval read p 4392008 = NetHack.Sokoban12CostPartition.d466 p := by
  change eval read p 4392008 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4392008 = .branch 160 3737602 3737606 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode137 p]
theorem oldNode467 (p : Pattern) : eval read p 4457776 = NetHack.Sokoban12CostPartition.d467 p := by
  change eval read p 4457776 = (if p 159 then NetHack.Sokoban12CostPartition.d466 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4457776 = .branch 159 3737602 4392008 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode466 p]
theorem oldNode468 (p : Pattern) : eval read p 4523412 = NetHack.Sokoban12CostPartition.d468 p := by
  change eval read p 4523412 = (if p 158 then NetHack.Sokoban12CostPartition.d467 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 4523412 = .branch 158 3737602 4457776 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode467 p]
theorem oldNode469 (p : Pattern) : eval read p 4392009 = NetHack.Sokoban12CostPartition.d469 p := by
  change eval read p 4392009 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 4392009 = .branch 160 3999608 3999611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode144 p]
theorem oldNode470 (p : Pattern) : eval read p 4457777 = NetHack.Sokoban12CostPartition.d470 p := by
  change eval read p 4457777 = (if p 159 then NetHack.Sokoban12CostPartition.d469 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 4457777 = .branch 159 3999608 4392009 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode469 p]
theorem oldNode471 (p : Pattern) : eval read p 4523413 = NetHack.Sokoban12CostPartition.d471 p := by
  change eval read p 4523413 = (if p 158 then NetHack.Sokoban12CostPartition.d470 p else NetHack.Sokoban12CostPartition.d62 p)
  have code : read 4523413 = .branch 158 3999608 4457777 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode62 p, oldNode470 p]
theorem oldNode472 (p : Pattern) : eval read p 4785008 = NetHack.Sokoban12CostPartition.d472 p := by
  change eval read p 4785008 = (if p 141 then NetHack.Sokoban12CostPartition.d471 p else NetHack.Sokoban12CostPartition.d468 p)
  have code : read 4785008 = .branch 141 4523412 4523413 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode468 p, oldNode471 p]
theorem oldNode473 (p : Pattern) : eval read p 4981423 = NetHack.Sokoban12CostPartition.d473 p := by
  change eval read p 4981423 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d472 p)
  have code : read 4981423 = .branch 134 4785008 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode472 p, oldNode66 p]
theorem oldNode474 (p : Pattern) : eval read p 4523414 = NetHack.Sokoban12CostPartition.d474 p := by
  change eval read p 4523414 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d466 p)
  have code : read 4523414 = .branch 158 4392008 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode466 p, oldNode55 p]
theorem oldNode475 (p : Pattern) : eval read p 4523415 = NetHack.Sokoban12CostPartition.d475 p := by
  change eval read p 4523415 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d469 p)
  have code : read 4523415 = .branch 158 4392009 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode469 p, oldNode65 p]
theorem oldNode476 (p : Pattern) : eval read p 4785009 = NetHack.Sokoban12CostPartition.d476 p := by
  change eval read p 4785009 = (if p 141 then NetHack.Sokoban12CostPartition.d475 p else NetHack.Sokoban12CostPartition.d474 p)
  have code : read 4785009 = .branch 141 4523414 4523415 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode474 p, oldNode475 p]
theorem oldNode477 (p : Pattern) : eval read p 4981424 = NetHack.Sokoban12CostPartition.d477 p := by
  change eval read p 4981424 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d476 p)
  have code : read 4981424 = .branch 134 4785009 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode476 p, oldNode66 p]
theorem oldNode478 (p : Pattern) : eval read p 5046764 = NetHack.Sokoban12CostPartition.d478 p := by
  change eval read p 5046764 = (if p 133 then NetHack.Sokoban12CostPartition.d477 p else NetHack.Sokoban12CostPartition.d473 p)
  have code : read 5046764 = .branch 133 4981423 4981424 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode473 p, oldNode477 p]
theorem oldNode479 (p : Pattern) : eval read p 4523416 = NetHack.Sokoban12CostPartition.d479 p := by
  change eval read p 4523416 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d467 p)
  have code : read 4523416 = .branch 158 4457776 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode467 p, oldNode55 p]
theorem oldNode480 (p : Pattern) : eval read p 4523417 = NetHack.Sokoban12CostPartition.d480 p := by
  change eval read p 4523417 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d470 p)
  have code : read 4523417 = .branch 158 4457777 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode470 p, oldNode65 p]
theorem oldNode481 (p : Pattern) : eval read p 4785010 = NetHack.Sokoban12CostPartition.d481 p := by
  change eval read p 4785010 = (if p 141 then NetHack.Sokoban12CostPartition.d480 p else NetHack.Sokoban12CostPartition.d479 p)
  have code : read 4785010 = .branch 141 4523416 4523417 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode479 p, oldNode480 p]
theorem oldNode482 (p : Pattern) : eval read p 4981425 = NetHack.Sokoban12CostPartition.d482 p := by
  change eval read p 4981425 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d481 p)
  have code : read 4981425 = .branch 134 4785010 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode481 p, oldNode66 p]
theorem oldNode483 (p : Pattern) : eval read p 5046765 = NetHack.Sokoban12CostPartition.d483 p := by
  change eval read p 5046765 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d482 p)
  have code : read 5046765 = .branch 133 4981425 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode482 p, oldNode66 p]
theorem oldNode484 (p : Pattern) : eval read p 5112174 = NetHack.Sokoban12CostPartition.d484 p := by
  change eval read p 5112174 = (if p 132 then NetHack.Sokoban12CostPartition.d483 p else NetHack.Sokoban12CostPartition.d478 p)
  have code : read 5112174 = .branch 132 5046764 5046765 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode478 p, oldNode483 p]
theorem oldNode485 (p : Pattern) : eval read p 5439697 = NetHack.Sokoban12CostPartition.d485 p := by
  change eval read p 5439697 = (if p 108 then NetHack.Sokoban12CostPartition.d484 p else NetHack.Sokoban12CostPartition.d465 p)
  have code : read 5439697 = .branch 108 5112173 5112174 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode465 p, oldNode484 p]
theorem oldNode501 (p : Pattern) : eval read p 4392010 = NetHack.Sokoban12CostPartition.d501 p := by
  change eval read p 4392010 = (if p 160 then NetHack.Sokoban12CostPartition.d137 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 4392010 = .branch 160 3671966 3737606 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode137 p]
theorem oldNode502 (p : Pattern) : eval read p 3999627 = NetHack.Sokoban12CostPartition.d502 p := by
  change eval read p 3999627 = (if p 168 then NetHack.Sokoban12CostPartition.d125 p else NetHack.Sokoban12CostPartition.d119 p)
  have code : read 3999627 = .branch 168 3671966 3671967 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode119 p, oldNode125 p]
theorem oldNode503 (p : Pattern) : eval read p 4392011 = NetHack.Sokoban12CostPartition.d503 p := by
  change eval read p 4392011 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d502 p)
  have code : read 4392011 = .branch 160 3999627 3999611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode502 p, oldNode144 p]
end NetHack.Soko12Forward220.Shared
