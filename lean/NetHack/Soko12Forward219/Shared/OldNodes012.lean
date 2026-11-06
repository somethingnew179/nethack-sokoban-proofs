import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode397 (p : Pattern) : eval read p 335927 = NetHack.Sokoban12CostPartition.d397 p := by
  change eval read p 335927 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d384 p)
  have code : read 335927 = .branch 158 327707 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode384 p, oldNode380 p]
theorem oldNode398 (p : Pattern) : eval read p 335928 = NetHack.Sokoban12CostPartition.d398 p := by
  change eval read p 335928 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d390 p)
  have code : read 335928 = .branch 158 327708 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode390 p, oldNode386 p]
theorem oldNode399 (p : Pattern) : eval read p 360485 = NetHack.Sokoban12CostPartition.d399 p := by
  change eval read p 360485 = (if p 141 then NetHack.Sokoban12CostPartition.d398 p else NetHack.Sokoban12CostPartition.d397 p)
  have code : read 360485 = .branch 141 335927 335928 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode397 p, oldNode398 p]
theorem oldNode400 (p : Pattern) : eval read p 368693 = NetHack.Sokoban12CostPartition.d400 p := by
  change eval read p 368693 = (if p 134 then NetHack.Sokoban12CostPartition.d399 p else NetHack.Sokoban12CostPartition.d396 p)
  have code : read 368693 = .branch 134 360484 360485 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode396 p, oldNode399 p]
theorem oldNode401 (p : Pattern) : eval read p 376890 = NetHack.Sokoban12CostPartition.d401 p := by
  change eval read p 376890 = (if p 133 then NetHack.Sokoban12CostPartition.d400 p else NetHack.Sokoban12CostPartition.d393 p)
  have code : read 376890 = .branch 133 368692 368693 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode393 p, oldNode400 p]
theorem oldNode402 (p : Pattern) : eval read p 360486 = NetHack.Sokoban12CostPartition.d402 p := by
  change eval read p 360486 = (if p 141 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d380 p)
  have code : read 360486 = .branch 141 286739 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode380 p, oldNode386 p]
theorem oldNode403 (p : Pattern) : eval read p 376891 = NetHack.Sokoban12CostPartition.d403 p := by
  change eval read p 376891 = (if p 133 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d400 p)
  have code : read 376891 = .branch 133 368693 360486 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode400 p, oldNode402 p]
theorem oldNode404 (p : Pattern) : eval read p 385060 = NetHack.Sokoban12CostPartition.d404 p := by
  change eval read p 385060 = (if p 132 then NetHack.Sokoban12CostPartition.d403 p else NetHack.Sokoban12CostPartition.d401 p)
  have code : read 385060 = .branch 132 376890 376891 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode401 p, oldNode403 p]
theorem oldNode405 (p : Pattern) : eval read p 286743 = NetHack.Sokoban12CostPartition.d405 p := by
  change eval read p 286743 = (if p 168 then NetHack.Sokoban12CostPartition.d290 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 286743 = .branch 168 270343 270349 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode290 p]
theorem oldNode406 (p : Pattern) : eval read p 319514 = NetHack.Sokoban12CostPartition.d406 p := by
  change eval read p 319514 = (if p 160 then NetHack.Sokoban12CostPartition.d405 p else NetHack.Sokoban12CostPartition.d382 p)
  have code : read 319514 = .branch 160 286740 286743 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode382 p, oldNode405 p]
theorem oldNode407 (p : Pattern) : eval read p 327709 = NetHack.Sokoban12CostPartition.d407 p := by
  change eval read p 327709 = (if p 159 then NetHack.Sokoban12CostPartition.d406 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 327709 = .branch 159 319508 319514 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode406 p]
theorem oldNode408 (p : Pattern) : eval read p 335929 = NetHack.Sokoban12CostPartition.d408 p := by
  change eval read p 335929 = (if p 158 then NetHack.Sokoban12CostPartition.d407 p else NetHack.Sokoban12CostPartition.d376 p)
  have code : read 335929 = .branch 158 319508 327709 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode376 p, oldNode407 p]
theorem oldNode409 (p : Pattern) : eval read p 286744 = NetHack.Sokoban12CostPartition.d409 p := by
  change eval read p 286744 = (if p 168 then NetHack.Sokoban12CostPartition.d291 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 286744 = .branch 168 270343 270350 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode291 p]
theorem oldNode410 (p : Pattern) : eval read p 319515 = NetHack.Sokoban12CostPartition.d410 p := by
  change eval read p 319515 = (if p 160 then NetHack.Sokoban12CostPartition.d409 p else NetHack.Sokoban12CostPartition.d388 p)
  have code : read 319515 = .branch 160 286742 286744 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode388 p, oldNode409 p]
theorem oldNode411 (p : Pattern) : eval read p 327710 = NetHack.Sokoban12CostPartition.d411 p := by
  change eval read p 327710 = (if p 159 then NetHack.Sokoban12CostPartition.d410 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 327710 = .branch 159 319509 319515 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode410 p]
theorem oldNode412 (p : Pattern) : eval read p 335930 = NetHack.Sokoban12CostPartition.d412 p := by
  change eval read p 335930 = (if p 158 then NetHack.Sokoban12CostPartition.d411 p else NetHack.Sokoban12CostPartition.d378 p)
  have code : read 335930 = .branch 158 319509 327710 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode378 p, oldNode411 p]
theorem oldNode413 (p : Pattern) : eval read p 360487 = NetHack.Sokoban12CostPartition.d413 p := by
  change eval read p 360487 = (if p 141 then NetHack.Sokoban12CostPartition.d412 p else NetHack.Sokoban12CostPartition.d408 p)
  have code : read 360487 = .branch 141 335929 335930 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode408 p, oldNode412 p]
theorem oldNode414 (p : Pattern) : eval read p 368694 = NetHack.Sokoban12CostPartition.d414 p := by
  change eval read p 368694 = (if p 134 then NetHack.Sokoban12CostPartition.d402 p else NetHack.Sokoban12CostPartition.d413 p)
  have code : read 368694 = .branch 134 360487 360486 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode413 p, oldNode402 p]
theorem oldNode415 (p : Pattern) : eval read p 319516 = NetHack.Sokoban12CostPartition.d415 p := by
  change eval read p 319516 = (if p 160 then NetHack.Sokoban12CostPartition.d405 p else NetHack.Sokoban12CostPartition.d21 p)
  have code : read 319516 = .branch 160 286722 286743 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode21 p, oldNode405 p]
theorem oldNode416 (p : Pattern) : eval read p 327711 = NetHack.Sokoban12CostPartition.d416 p := by
  change eval read p 327711 = (if p 159 then NetHack.Sokoban12CostPartition.d406 p else NetHack.Sokoban12CostPartition.d415 p)
  have code : read 327711 = .branch 159 319516 319514 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode415 p, oldNode406 p]
theorem oldNode417 (p : Pattern) : eval read p 335931 = NetHack.Sokoban12CostPartition.d417 p := by
  change eval read p 335931 = (if p 158 then NetHack.Sokoban12CostPartition.d380 p else NetHack.Sokoban12CostPartition.d416 p)
  have code : read 335931 = .branch 158 327711 286739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode416 p, oldNode380 p]
theorem oldNode418 (p : Pattern) : eval read p 319517 = NetHack.Sokoban12CostPartition.d418 p := by
  change eval read p 319517 = (if p 160 then NetHack.Sokoban12CostPartition.d409 p else NetHack.Sokoban12CostPartition.d22 p)
  have code : read 319517 = .branch 160 286723 286744 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode22 p, oldNode409 p]
theorem oldNode419 (p : Pattern) : eval read p 327712 = NetHack.Sokoban12CostPartition.d419 p := by
  change eval read p 327712 = (if p 159 then NetHack.Sokoban12CostPartition.d410 p else NetHack.Sokoban12CostPartition.d418 p)
  have code : read 327712 = .branch 159 319517 319515 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode418 p, oldNode410 p]
theorem oldNode420 (p : Pattern) : eval read p 335932 = NetHack.Sokoban12CostPartition.d420 p := by
  change eval read p 335932 = (if p 158 then NetHack.Sokoban12CostPartition.d386 p else NetHack.Sokoban12CostPartition.d419 p)
  have code : read 335932 = .branch 158 327712 286741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode419 p, oldNode386 p]
end NetHack.Soko12Forward219.Shared
