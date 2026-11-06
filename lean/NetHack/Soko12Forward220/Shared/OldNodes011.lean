import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode373 (p : Pattern) : eval read p 5112170 = NetHack.Sokoban12CostPartition.d373 p := by
  change eval read p 5112170 = (if p 132 then NetHack.Sokoban12CostPartition.d372 p else NetHack.Sokoban12CostPartition.d371 p)
  have code : read 5112170 = .branch 132 5046756 5046757 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode371 p, oldNode372 p]
theorem oldNode374 (p : Pattern) : eval read p 5439695 = NetHack.Sokoban12CostPartition.d374 p := by
  change eval read p 5439695 = (if p 108 then NetHack.Sokoban12CostPartition.d373 p else NetHack.Sokoban12CostPartition.d368 p)
  have code : read 5439695 = .branch 108 5112169 5112170 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode368 p, oldNode373 p]
theorem oldNode375 (p : Pattern) : eval read p 3999618 = NetHack.Sokoban12CostPartition.d375 p := by
  change eval read p 3999618 = (if p 168 then NetHack.Sokoban12CostPartition.d261 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 3999618 = .branch 168 3737602 3737608 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode261 p]
theorem oldNode376 (p : Pattern) : eval read p 4391996 = NetHack.Sokoban12CostPartition.d376 p := by
  change eval read p 4391996 = (if p 160 then NetHack.Sokoban12CostPartition.d375 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 4391996 = .branch 160 3999617 3999618 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode375 p]
theorem oldNode377 (p : Pattern) : eval read p 3999620 = NetHack.Sokoban12CostPartition.d377 p := by
  change eval read p 3999620 = (if p 168 then NetHack.Sokoban12CostPartition.d265 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 3999620 = .branch 168 3737602 3737609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode265 p]
theorem oldNode378 (p : Pattern) : eval read p 4391997 = NetHack.Sokoban12CostPartition.d378 p := by
  change eval read p 4391997 = (if p 160 then NetHack.Sokoban12CostPartition.d377 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 4391997 = .branch 160 3999619 3999620 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode377 p]
theorem oldNode379 (p : Pattern) : eval read p 4784996 = NetHack.Sokoban12CostPartition.d379 p := by
  change eval read p 4784996 = (if p 141 then NetHack.Sokoban12CostPartition.d378 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 4784996 = .branch 141 4391996 4391997 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode378 p]
theorem oldNode380 (p : Pattern) : eval read p 3999621 = NetHack.Sokoban12CostPartition.d380 p := by
  change eval read p 3999621 = (if p 168 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 3999621 = .branch 168 3411913 3411918 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode260 p]
theorem oldNode381 (p : Pattern) : eval read p 4391998 = NetHack.Sokoban12CostPartition.d381 p := by
  change eval read p 4391998 = (if p 160 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 4391998 = .branch 160 3999617 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode380 p]
theorem oldNode382 (p : Pattern) : eval read p 3999622 = NetHack.Sokoban12CostPartition.d382 p := by
  change eval read p 3999622 = (if p 168 then NetHack.Sokoban12CostPartition.d272 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 3999622 = .branch 168 3737604 3737610 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode272 p]
theorem oldNode383 (p : Pattern) : eval read p 4391999 = NetHack.Sokoban12CostPartition.d383 p := by
  change eval read p 4391999 = (if p 160 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d382 p)
  have code : read 4391999 = .branch 160 3999622 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode382 p, oldNode380 p]
theorem oldNode384 (p : Pattern) : eval read p 4457770 = NetHack.Sokoban12CostPartition.d384 p := by
  change eval read p 4457770 = (if p 159 then NetHack.Sokoban12CostPartition.d383 p else NetHack.Sokoban12CostPartition.d381 p)
  have code : read 4457770 = .branch 159 4391998 4391999 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode381 p, oldNode383 p]
theorem oldNode385 (p : Pattern) : eval read p 4523396 = NetHack.Sokoban12CostPartition.d385 p := by
  change eval read p 4523396 = (if p 158 then NetHack.Sokoban12CostPartition.d384 p else NetHack.Sokoban12CostPartition.d381 p)
  have code : read 4523396 = .branch 158 4391998 4457770 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode381 p, oldNode384 p]
theorem oldNode386 (p : Pattern) : eval read p 3999623 = NetHack.Sokoban12CostPartition.d386 p := by
  change eval read p 3999623 = (if p 168 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 3999623 = .branch 168 3411913 3411919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode264 p]
theorem oldNode387 (p : Pattern) : eval read p 4392000 = NetHack.Sokoban12CostPartition.d387 p := by
  change eval read p 4392000 = (if p 160 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 4392000 = .branch 160 3999619 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode386 p]
theorem oldNode388 (p : Pattern) : eval read p 3999624 = NetHack.Sokoban12CostPartition.d388 p := by
  change eval read p 3999624 = (if p 168 then NetHack.Sokoban12CostPartition.d274 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 3999624 = .branch 168 3737604 3737611 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode274 p]
theorem oldNode389 (p : Pattern) : eval read p 4392001 = NetHack.Sokoban12CostPartition.d389 p := by
  change eval read p 4392001 = (if p 160 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d388 p)
  have code : read 4392001 = .branch 160 3999624 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode388 p, oldNode386 p]
theorem oldNode390 (p : Pattern) : eval read p 4457771 = NetHack.Sokoban12CostPartition.d390 p := by
  change eval read p 4457771 = (if p 159 then NetHack.Sokoban12CostPartition.d389 p else NetHack.Sokoban12CostPartition.d387 p)
  have code : read 4457771 = .branch 159 4392000 4392001 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode387 p, oldNode389 p]
theorem oldNode391 (p : Pattern) : eval read p 4523397 = NetHack.Sokoban12CostPartition.d391 p := by
  change eval read p 4523397 = (if p 158 then NetHack.Sokoban12CostPartition.d390 p else NetHack.Sokoban12CostPartition.d387 p)
  have code : read 4523397 = .branch 158 4392000 4457771 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode387 p, oldNode390 p]
theorem oldNode392 (p : Pattern) : eval read p 4784997 = NetHack.Sokoban12CostPartition.d392 p := by
  change eval read p 4784997 = (if p 141 then NetHack.Sokoban12CostPartition.d391 p else NetHack.Sokoban12CostPartition.d385 p)
  have code : read 4784997 = .branch 141 4523396 4523397 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode385 p, oldNode391 p]
theorem oldNode393 (p : Pattern) : eval read p 4981416 = NetHack.Sokoban12CostPartition.d393 p := by
  change eval read p 4981416 = (if p 134 then NetHack.Sokoban12CostPartition.d392 p else NetHack.Sokoban12CostPartition.d379 p)
  have code : read 4981416 = .branch 134 4784996 4784997 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode379 p, oldNode392 p]
theorem oldNode394 (p : Pattern) : eval read p 4523398 = NetHack.Sokoban12CostPartition.d394 p := by
  change eval read p 4523398 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 4523398 = .branch 158 4391996 3999621 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode380 p]
theorem oldNode395 (p : Pattern) : eval read p 4523399 = NetHack.Sokoban12CostPartition.d395 p := by
  change eval read p 4523399 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 4523399 = .branch 158 4391997 3999623 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode386 p]
theorem oldNode396 (p : Pattern) : eval read p 4784998 = NetHack.Sokoban12CostPartition.d396 p := by
  change eval read p 4784998 = (if p 141 then NetHack.Sokoban12CostPartition.d395 p else NetHack.Sokoban12CostPartition.d394 p)
  have code : read 4784998 = .branch 141 4523398 4523399 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode394 p, oldNode395 p]
end NetHack.Soko12Forward220.Shared
