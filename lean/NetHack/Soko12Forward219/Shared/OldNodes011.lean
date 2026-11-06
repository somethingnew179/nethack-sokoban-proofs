import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode373 (p : Pattern) : eval read p 385059 = NetHack.Sokoban12CostPartition.d373 p := by
  change eval read p 385059 = (if p 132 then NetHack.Sokoban12CostPartition.d372 p else NetHack.Sokoban12CostPartition.d371 p)
  have code : read 385059 = .branch 132 376888 376889 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode371 p, oldNode372 p]
theorem oldNode374 (p : Pattern) : eval read p 409619 = NetHack.Sokoban12CostPartition.d374 p := by
  change eval read p 409619 = (if p 108 then NetHack.Sokoban12CostPartition.d373 p else NetHack.Sokoban12CostPartition.d368 p)
  have code : read 409619 = .branch 108 385058 385059 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode368 p, oldNode373 p]
theorem oldNode375 (p : Pattern) : eval read p 286737 = NetHack.Sokoban12CostPartition.d375 p := by
  change eval read p 286737 = (if p 168 then NetHack.Sokoban12CostPartition.d261 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 286737 = .branch 168 270337 270345 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode261 p]
theorem oldNode376 (p : Pattern) : eval read p 319508 = NetHack.Sokoban12CostPartition.d376 p := by
  change eval read p 319508 = (if p 160 then NetHack.Sokoban12CostPartition.d375 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 319508 = .branch 160 286722 286737 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode375 p]
theorem oldNode377 (p : Pattern) : eval read p 286738 = NetHack.Sokoban12CostPartition.d377 p := by
  change eval read p 286738 = (if p 168 then NetHack.Sokoban12CostPartition.d265 p else NetHack.Sokoban12CostPartition.d56 p)
  have code : read 286738 = .branch 168 270337 270346 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode56 p, oldNode265 p]
theorem oldNode378 (p : Pattern) : eval read p 319509 = NetHack.Sokoban12CostPartition.d378 p := by
  change eval read p 319509 = (if p 160 then NetHack.Sokoban12CostPartition.d377 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 319509 = .branch 160 286723 286738 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode377 p]
theorem oldNode379 (p : Pattern) : eval read p 360482 = NetHack.Sokoban12CostPartition.d379 p := by
  change eval read p 360482 = (if p 141 then NetHack.Sokoban12CostPartition.d378 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 360482 = .branch 141 319508 319509 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode378 p]
theorem oldNode380 (p : Pattern) : eval read p 286739 = NetHack.Sokoban12CostPartition.d380 p := by
  change eval read p 286739 = (if p 168 then NetHack.Sokoban12CostPartition.d260 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 286739 = .branch 168 229387 229389 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode260 p]
theorem oldNode381 (p : Pattern) : eval read p 319510 = NetHack.Sokoban12CostPartition.d381 p := by
  change eval read p 319510 = (if p 160 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 319510 = .branch 160 286722 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode380 p]
theorem oldNode382 (p : Pattern) : eval read p 286740 = NetHack.Sokoban12CostPartition.d382 p := by
  change eval read p 286740 = (if p 168 then NetHack.Sokoban12CostPartition.d272 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 286740 = .branch 168 270341 270347 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode272 p]
theorem oldNode383 (p : Pattern) : eval read p 319511 = NetHack.Sokoban12CostPartition.d383 p := by
  change eval read p 319511 = (if p 160 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d382 p)
  have code : read 319511 = .branch 160 286740 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode382 p, oldNode380 p]
theorem oldNode384 (p : Pattern) : eval read p 327707 = NetHack.Sokoban12CostPartition.d384 p := by
  change eval read p 327707 = (if p 159 then NetHack.Sokoban12CostPartition.d383 p else NetHack.Sokoban12CostPartition.d381 p)
  have code : read 327707 = .branch 159 319510 319511 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode381 p, oldNode383 p]
theorem oldNode385 (p : Pattern) : eval read p 335923 = NetHack.Sokoban12CostPartition.d385 p := by
  change eval read p 335923 = (if p 158 then NetHack.Sokoban12CostPartition.d384 p else NetHack.Sokoban12CostPartition.d381 p)
  have code : read 335923 = .branch 158 319510 327707 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode381 p, oldNode384 p]
theorem oldNode386 (p : Pattern) : eval read p 286741 = NetHack.Sokoban12CostPartition.d386 p := by
  change eval read p 286741 = (if p 168 then NetHack.Sokoban12CostPartition.d264 p else NetHack.Sokoban12CostPartition.d55 p)
  have code : read 286741 = .branch 168 229387 229390 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode55 p, oldNode264 p]
theorem oldNode387 (p : Pattern) : eval read p 319512 = NetHack.Sokoban12CostPartition.d387 p := by
  change eval read p 319512 = (if p 160 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 319512 = .branch 160 286723 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode386 p]
theorem oldNode388 (p : Pattern) : eval read p 286742 = NetHack.Sokoban12CostPartition.d388 p := by
  change eval read p 286742 = (if p 168 then NetHack.Sokoban12CostPartition.d274 p else NetHack.Sokoban12CostPartition.d120 p)
  have code : read 286742 = .branch 168 270341 270348 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode120 p, oldNode274 p]
theorem oldNode389 (p : Pattern) : eval read p 319513 = NetHack.Sokoban12CostPartition.d389 p := by
  change eval read p 319513 = (if p 160 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d388 p)
  have code : read 319513 = .branch 160 286742 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode388 p, oldNode386 p]
theorem oldNode390 (p : Pattern) : eval read p 327708 = NetHack.Sokoban12CostPartition.d390 p := by
  change eval read p 327708 = (if p 159 then NetHack.Sokoban12CostPartition.d389 p else NetHack.Sokoban12CostPartition.d387 p)
  have code : read 327708 = .branch 159 319512 319513 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode387 p, oldNode389 p]
theorem oldNode391 (p : Pattern) : eval read p 335924 = NetHack.Sokoban12CostPartition.d391 p := by
  change eval read p 335924 = (if p 158 then NetHack.Sokoban12CostPartition.d390 p else NetHack.Sokoban12CostPartition.d387 p)
  have code : read 335924 = .branch 158 319512 327708 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode387 p, oldNode390 p]
theorem oldNode392 (p : Pattern) : eval read p 360483 = NetHack.Sokoban12CostPartition.d392 p := by
  change eval read p 360483 = (if p 141 then NetHack.Sokoban12CostPartition.d391 p else NetHack.Sokoban12CostPartition.d385 p)
  have code : read 360483 = .branch 141 335923 335924 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode385 p, oldNode391 p]
theorem oldNode393 (p : Pattern) : eval read p 368692 = NetHack.Sokoban12CostPartition.d393 p := by
  change eval read p 368692 = (if p 134 then NetHack.Sokoban12CostPartition.d392 p else NetHack.Sokoban12CostPartition.d379 p)
  have code : read 368692 = .branch 134 360482 360483 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode379 p, oldNode392 p]
theorem oldNode394 (p : Pattern) : eval read p 335925 = NetHack.Sokoban12CostPartition.d394 p := by
  change eval read p 335925 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 335925 = .branch 158 319508 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode380 p]
theorem oldNode395 (p : Pattern) : eval read p 335926 = NetHack.Sokoban12CostPartition.d395 p := by
  change eval read p 335926 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 335926 = .branch 158 319509 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode386 p]
theorem oldNode396 (p : Pattern) : eval read p 360484 = NetHack.Sokoban12CostPartition.d396 p := by
  change eval read p 360484 = (if p 141 then NetHack.Sokoban12CostPartition.d395 p else NetHack.Sokoban12CostPartition.d394 p)
  have code : read 360484 = .branch 141 335925 335926 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode394 p, oldNode395 p]
end NetHack.Soko12Forward219.Shared
