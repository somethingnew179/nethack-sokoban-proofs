import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode397 (p : Pattern) : eval read p 4523400 = NetHack.Sokoban12CostPartition.d397 p := by
  change eval read p 4523400 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d384 p)
  have code : read 4523400 = .branch 158 4457770 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode384 p, oldNode380 p]
theorem oldNode398 (p : Pattern) : eval read p 4523401 = NetHack.Sokoban12CostPartition.d398 p := by
  change eval read p 4523401 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d390 p)
  have code : read 4523401 = .branch 158 4457771 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode390 p, oldNode386 p]
theorem oldNode399 (p : Pattern) : eval read p 4784999 = NetHack.Sokoban12CostPartition.d399 p := by
  change eval read p 4784999 = (if p 141 then NetHack.Sokoban12CostPartition.d398 p else NetHack.Sokoban12CostPartition.d397 p)
  have code : read 4784999 = .branch 141 4523400 4523401 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode397 p, oldNode398 p]
theorem oldNode400 (p : Pattern) : eval read p 4981417 = NetHack.Sokoban12CostPartition.d400 p := by
  change eval read p 4981417 = (if p 134 then NetHack.Sokoban12CostPartition.d399 p else NetHack.Sokoban12CostPartition.d396 p)
  have code : read 4981417 = .branch 134 4784998 4784999 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode396 p, oldNode399 p]
theorem oldNode401 (p : Pattern) : eval read p 5046758 = NetHack.Sokoban12CostPartition.d401 p := by
  change eval read p 5046758 = (if p 133 then NetHack.Sokoban12CostPartition.d400 p else NetHack.Sokoban12CostPartition.d393 p)
  have code : read 5046758 = .branch 133 4981416 4981417 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode393 p, oldNode400 p]
theorem oldNode402 (p : Pattern) : eval read p 4785000 = NetHack.Sokoban12CostPartition.d402 p := by
  change eval read p 4785000 = (if p 141 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d380 p)
  have code : read 4785000 = .branch 141 3999621 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode380 p, oldNode386 p]
theorem oldNode403 (p : Pattern) : eval read p 5046759 = NetHack.Sokoban12CostPartition.d403 p := by
  change eval read p 5046759 = (if p 133 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d400 p)
  have code : read 5046759 = .branch 133 4981417 4785000 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode400 p, oldNode402 p]
theorem oldNode404 (p : Pattern) : eval read p 5112171 = NetHack.Sokoban12CostPartition.d404 p := by
  change eval read p 5112171 = (if p 132 then NetHack.Sokoban12CostPartition.d403 p else NetHack.Sokoban12CostPartition.d401 p)
  have code : read 5112171 = .branch 132 5046758 5046759 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode401 p, oldNode403 p]
theorem oldNode405 (p : Pattern) : eval read p 3999625 = NetHack.Sokoban12CostPartition.d405 p := by
  change eval read p 3999625 = (if p 168 then NetHack.Sokoban12CostPartition.d290 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 3999625 = .branch 168 3737606 3737612 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode290 p]
theorem oldNode406 (p : Pattern) : eval read p 4392002 = NetHack.Sokoban12CostPartition.d406 p := by
  change eval read p 4392002 = (if p 160 then NetHack.Sokoban12CostPartition.d405 p else NetHack.Sokoban12CostPartition.d382 p)
  have code : read 4392002 = .branch 160 3999622 3999625 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode382 p, oldNode405 p]
theorem oldNode407 (p : Pattern) : eval read p 4457772 = NetHack.Sokoban12CostPartition.d407 p := by
  change eval read p 4457772 = (if p 159 then NetHack.Sokoban12CostPartition.d406 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 4457772 = .branch 159 4391996 4392002 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode406 p]
theorem oldNode408 (p : Pattern) : eval read p 4523402 = NetHack.Sokoban12CostPartition.d408 p := by
  change eval read p 4523402 = (if p 158 then NetHack.Sokoban12CostPartition.d407 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 4523402 = .branch 158 4391996 4457772 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode407 p]
theorem oldNode409 (p : Pattern) : eval read p 3999626 = NetHack.Sokoban12CostPartition.d409 p := by
  change eval read p 3999626 = (if p 168 then NetHack.Sokoban12CostPartition.d291 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 3999626 = .branch 168 3737606 3737613 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode291 p]
theorem oldNode410 (p : Pattern) : eval read p 4392003 = NetHack.Sokoban12CostPartition.d410 p := by
  change eval read p 4392003 = (if p 160 then NetHack.Sokoban12CostPartition.d409 p else NetHack.Sokoban12CostPartition.d388 p)
  have code : read 4392003 = .branch 160 3999624 3999626 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode388 p, oldNode409 p]
theorem oldNode411 (p : Pattern) : eval read p 4457773 = NetHack.Sokoban12CostPartition.d411 p := by
  change eval read p 4457773 = (if p 159 then NetHack.Sokoban12CostPartition.d410 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 4457773 = .branch 159 4391997 4392003 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode410 p]
theorem oldNode412 (p : Pattern) : eval read p 4523403 = NetHack.Sokoban12CostPartition.d412 p := by
  change eval read p 4523403 = (if p 158 then NetHack.Sokoban12CostPartition.d411 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 4523403 = .branch 158 4391997 4457773 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode411 p]
theorem oldNode413 (p : Pattern) : eval read p 4785001 = NetHack.Sokoban12CostPartition.d413 p := by
  change eval read p 4785001 = (if p 141 then NetHack.Sokoban12CostPartition.d412 p else NetHack.Sokoban12CostPartition.d408 p)
  have code : read 4785001 = .branch 141 4523402 4523403 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode408 p, oldNode412 p]
theorem oldNode414 (p : Pattern) : eval read p 4981418 = NetHack.Sokoban12CostPartition.d414 p := by
  change eval read p 4981418 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d413 p)
  have code : read 4981418 = .branch 134 4785001 4785000 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode413 p, oldNode402 p]
theorem oldNode415 (p : Pattern) : eval read p 4392004 = NetHack.Sokoban12CostPartition.d415 p := by
  change eval read p 4392004 = (if p 160 then NetHack.Sokoban12CostPartition.d405 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 4392004 = .branch 160 3999617 3999625 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode405 p]
theorem oldNode416 (p : Pattern) : eval read p 4457774 = NetHack.Sokoban12CostPartition.d416 p := by
  change eval read p 4457774 = (if p 159 then NetHack.Sokoban12CostPartition.d406 p else NetHack.Sokoban12CostPartition.d415 p)
  have code : read 4457774 = .branch 159 4392004 4392002 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode415 p, oldNode406 p]
theorem oldNode417 (p : Pattern) : eval read p 4523404 = NetHack.Sokoban12CostPartition.d417 p := by
  change eval read p 4523404 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d416 p)
  have code : read 4523404 = .branch 158 4457774 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode416 p, oldNode380 p]
theorem oldNode418 (p : Pattern) : eval read p 4392005 = NetHack.Sokoban12CostPartition.d418 p := by
  change eval read p 4392005 = (if p 160 then NetHack.Sokoban12CostPartition.d409 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 4392005 = .branch 160 3999619 3999626 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode409 p]
theorem oldNode419 (p : Pattern) : eval read p 4457775 = NetHack.Sokoban12CostPartition.d419 p := by
  change eval read p 4457775 = (if p 159 then NetHack.Sokoban12CostPartition.d410 p else NetHack.Sokoban12CostPartition.d418 p)
  have code : read 4457775 = .branch 159 4392005 4392003 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode418 p, oldNode410 p]
theorem oldNode420 (p : Pattern) : eval read p 4523405 = NetHack.Sokoban12CostPartition.d420 p := by
  change eval read p 4523405 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d419 p)
  have code : read 4523405 = .branch 158 4457775 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode419 p, oldNode386 p]
end NetHack.Soko12Forward220.Shared
