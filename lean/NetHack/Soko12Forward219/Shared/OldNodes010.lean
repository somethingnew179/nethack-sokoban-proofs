import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode340 (p : Pattern) : eval read p 360480 = NetHack.Sokoban12CostPartition.d340 p := by
  change eval read p 360480 = (if p 141 then NetHack.Sokoban12CostPartition.d339 p else NetHack.Sokoban12CostPartition.d338 p)
  have code : read 360480 = .branch 141 335919 335920 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode338 p, oldNode339 p]
theorem oldNode341 (p : Pattern) : eval read p 368684 = NetHack.Sokoban12CostPartition.d341 p := by
  change eval read p 368684 = (if p 134 then NetHack.Sokoban12CostPartition.d213 p else NetHack.Sokoban12CostPartition.d340 p)
  have code : read 368684 = .branch 134 360480 360462 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode340 p, oldNode213 p]
theorem oldNode342 (p : Pattern) : eval read p 376878 = NetHack.Sokoban12CostPartition.d342 p := by
  change eval read p 376878 = (if p 133 then NetHack.Sokoban12CostPartition.d341 p else NetHack.Sokoban12CostPartition.d337 p)
  have code : read 376878 = .branch 133 368683 368684 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode337 p, oldNode341 p]
theorem oldNode343 (p : Pattern) : eval read p 376879 = NetHack.Sokoban12CostPartition.d343 p := by
  change eval read p 376879 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d341 p)
  have code : read 376879 = .branch 133 368684 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode341 p, oldNode66 p]
theorem oldNode344 (p : Pattern) : eval read p 385054 = NetHack.Sokoban12CostPartition.d344 p := by
  change eval read p 385054 = (if p 132 then NetHack.Sokoban12CostPartition.d343 p else NetHack.Sokoban12CostPartition.d342 p)
  have code : read 385054 = .branch 132 376878 376879 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode342 p, oldNode343 p]
theorem oldNode345 (p : Pattern) : eval read p 368685 = NetHack.Sokoban12CostPartition.d345 p := by
  change eval read p 368685 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d335 p)
  have code : read 368685 = .branch 134 360478 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode335 p, oldNode66 p]
theorem oldNode346 (p : Pattern) : eval read p 327705 = NetHack.Sokoban12CostPartition.d346 p := by
  change eval read p 327705 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d138 p)
  have code : read 327705 = .branch 159 319499 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode138 p, oldNode55 p]
theorem oldNode347 (p : Pattern) : eval read p 335921 = NetHack.Sokoban12CostPartition.d347 p := by
  change eval read p 335921 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d346 p)
  have code : read 335921 = .branch 158 327705 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode346 p, oldNode55 p]
theorem oldNode348 (p : Pattern) : eval read p 327706 = NetHack.Sokoban12CostPartition.d348 p := by
  change eval read p 327706 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d145 p)
  have code : read 327706 = .branch 159 319501 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode145 p, oldNode65 p]
theorem oldNode349 (p : Pattern) : eval read p 335922 = NetHack.Sokoban12CostPartition.d349 p := by
  change eval read p 335922 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d348 p)
  have code : read 335922 = .branch 158 327706 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode348 p, oldNode65 p]
theorem oldNode350 (p : Pattern) : eval read p 360481 = NetHack.Sokoban12CostPartition.d350 p := by
  change eval read p 360481 = (if p 141 then NetHack.Sokoban12CostPartition.d349 p else NetHack.Sokoban12CostPartition.d347 p)
  have code : read 360481 = .branch 141 335921 335922 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode347 p, oldNode349 p]
theorem oldNode351 (p : Pattern) : eval read p 368686 = NetHack.Sokoban12CostPartition.d351 p := by
  change eval read p 368686 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d350 p)
  have code : read 368686 = .branch 134 360481 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode350 p, oldNode66 p]
theorem oldNode352 (p : Pattern) : eval read p 376880 = NetHack.Sokoban12CostPartition.d352 p := by
  change eval read p 376880 = (if p 133 then NetHack.Sokoban12CostPartition.d351 p else NetHack.Sokoban12CostPartition.d345 p)
  have code : read 376880 = .branch 133 368685 368686 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode345 p, oldNode351 p]
theorem oldNode353 (p : Pattern) : eval read p 368687 = NetHack.Sokoban12CostPartition.d353 p := by
  change eval read p 368687 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d340 p)
  have code : read 368687 = .branch 134 360480 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode340 p, oldNode66 p]
theorem oldNode354 (p : Pattern) : eval read p 376881 = NetHack.Sokoban12CostPartition.d354 p := by
  change eval read p 376881 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d353 p)
  have code : read 376881 = .branch 133 368687 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode353 p, oldNode66 p]
theorem oldNode355 (p : Pattern) : eval read p 385055 = NetHack.Sokoban12CostPartition.d355 p := by
  change eval read p 385055 = (if p 132 then NetHack.Sokoban12CostPartition.d354 p else NetHack.Sokoban12CostPartition.d352 p)
  have code : read 385055 = .branch 132 376880 376881 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode352 p, oldNode354 p]
theorem oldNode356 (p : Pattern) : eval read p 409617 = NetHack.Sokoban12CostPartition.d356 p := by
  change eval read p 409617 = (if p 108 then NetHack.Sokoban12CostPartition.d355 p else NetHack.Sokoban12CostPartition.d344 p)
  have code : read 409617 = .branch 108 385054 385055 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode344 p, oldNode355 p]
theorem oldNode366 (p : Pattern) : eval read p 376886 = NetHack.Sokoban12CostPartition.d366 p := by
  change eval read p 376886 = (if p 133 then NetHack.Sokoban12CostPartition.d231 p else NetHack.Sokoban12CostPartition.d227 p)
  have code : read 376886 = .branch 133 360463 360464 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode227 p, oldNode231 p]
theorem oldNode367 (p : Pattern) : eval read p 376887 = NetHack.Sokoban12CostPartition.d367 p := by
  change eval read p 376887 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d231 p)
  have code : read 376887 = .branch 133 360464 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode231 p, oldNode66 p]
theorem oldNode368 (p : Pattern) : eval read p 385058 = NetHack.Sokoban12CostPartition.d368 p := by
  change eval read p 385058 = (if p 132 then NetHack.Sokoban12CostPartition.d367 p else NetHack.Sokoban12CostPartition.d366 p)
  have code : read 385058 = .branch 132 376886 376887 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode366 p, oldNode367 p]
theorem oldNode369 (p : Pattern) : eval read p 368690 = NetHack.Sokoban12CostPartition.d369 p := by
  change eval read p 368690 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d227 p)
  have code : read 368690 = .branch 134 360463 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode227 p, oldNode66 p]
theorem oldNode370 (p : Pattern) : eval read p 368691 = NetHack.Sokoban12CostPartition.d370 p := by
  change eval read p 368691 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d231 p)
  have code : read 368691 = .branch 134 360464 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode231 p, oldNode66 p]
theorem oldNode371 (p : Pattern) : eval read p 376888 = NetHack.Sokoban12CostPartition.d371 p := by
  change eval read p 376888 = (if p 133 then NetHack.Sokoban12CostPartition.d370 p else NetHack.Sokoban12CostPartition.d369 p)
  have code : read 376888 = .branch 133 368690 368691 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode369 p, oldNode370 p]
theorem oldNode372 (p : Pattern) : eval read p 376889 = NetHack.Sokoban12CostPartition.d372 p := by
  change eval read p 376889 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d370 p)
  have code : read 376889 = .branch 133 368691 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode370 p, oldNode66 p]
end NetHack.Soko12Forward219.Shared
