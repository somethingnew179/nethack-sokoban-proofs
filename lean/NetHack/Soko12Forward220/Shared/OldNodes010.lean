import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode340 (p : Pattern) : eval read p 4784994 = NetHack.Sokoban12CostPartition.d340 p := by
  change eval read p 4784994 = (if p 141 then NetHack.Sokoban12CostPartition.d339 p else NetHack.Sokoban12CostPartition.d338 p)
  have code : read 4784994 = .branch 141 4523392 4523393 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode338 p, oldNode339 p]
theorem oldNode341 (p : Pattern) : eval read p 4981410 = NetHack.Sokoban12CostPartition.d341 p := by
  change eval read p 4981410 = (if p 134 then NetHack.Sokoban12CostPartition.d213 p else NetHack.Sokoban12CostPartition.d340 p)
  have code : read 4981410 = .branch 134 4784994 4784976 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode340 p, oldNode213 p]
theorem oldNode342 (p : Pattern) : eval read p 5046750 = NetHack.Sokoban12CostPartition.d342 p := by
  change eval read p 5046750 = (if p 133 then NetHack.Sokoban12CostPartition.d341 p else NetHack.Sokoban12CostPartition.d337 p)
  have code : read 5046750 = .branch 133 4981409 4981410 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode337 p, oldNode341 p]
theorem oldNode343 (p : Pattern) : eval read p 5046751 = NetHack.Sokoban12CostPartition.d343 p := by
  change eval read p 5046751 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d341 p)
  have code : read 5046751 = .branch 133 4981410 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode341 p, oldNode66 p]
theorem oldNode344 (p : Pattern) : eval read p 5112167 = NetHack.Sokoban12CostPartition.d344 p := by
  change eval read p 5112167 = (if p 132 then NetHack.Sokoban12CostPartition.d343 p else NetHack.Sokoban12CostPartition.d342 p)
  have code : read 5112167 = .branch 132 5046750 5046751 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode342 p, oldNode343 p]
theorem oldNode345 (p : Pattern) : eval read p 4981411 = NetHack.Sokoban12CostPartition.d345 p := by
  change eval read p 4981411 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d335 p)
  have code : read 4981411 = .branch 134 4784992 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode335 p, oldNode66 p]
theorem oldNode346 (p : Pattern) : eval read p 4457768 = NetHack.Sokoban12CostPartition.d346 p := by
  change eval read p 4457768 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d138 p)
  have code : read 4457768 = .branch 159 4391987 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode138 p, oldNode55 p]
theorem oldNode347 (p : Pattern) : eval read p 4523394 = NetHack.Sokoban12CostPartition.d347 p := by
  change eval read p 4523394 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d346 p)
  have code : read 4523394 = .branch 158 4457768 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode346 p, oldNode55 p]
theorem oldNode348 (p : Pattern) : eval read p 4457769 = NetHack.Sokoban12CostPartition.d348 p := by
  change eval read p 4457769 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d145 p)
  have code : read 4457769 = .branch 159 4391989 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode145 p, oldNode65 p]
theorem oldNode349 (p : Pattern) : eval read p 4523395 = NetHack.Sokoban12CostPartition.d349 p := by
  change eval read p 4523395 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d348 p)
  have code : read 4523395 = .branch 158 4457769 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode348 p, oldNode65 p]
theorem oldNode350 (p : Pattern) : eval read p 4784995 = NetHack.Sokoban12CostPartition.d350 p := by
  change eval read p 4784995 = (if p 141 then NetHack.Sokoban12CostPartition.d349 p else NetHack.Sokoban12CostPartition.d347 p)
  have code : read 4784995 = .branch 141 4523394 4523395 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode347 p, oldNode349 p]
theorem oldNode351 (p : Pattern) : eval read p 4981412 = NetHack.Sokoban12CostPartition.d351 p := by
  change eval read p 4981412 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d350 p)
  have code : read 4981412 = .branch 134 4784995 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode350 p, oldNode66 p]
theorem oldNode352 (p : Pattern) : eval read p 5046752 = NetHack.Sokoban12CostPartition.d352 p := by
  change eval read p 5046752 = (if p 133 then NetHack.Sokoban12CostPartition.d351 p else NetHack.Sokoban12CostPartition.d345 p)
  have code : read 5046752 = .branch 133 4981411 4981412 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode345 p, oldNode351 p]
theorem oldNode353 (p : Pattern) : eval read p 4981413 = NetHack.Sokoban12CostPartition.d353 p := by
  change eval read p 4981413 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d340 p)
  have code : read 4981413 = .branch 134 4784994 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode340 p, oldNode66 p]
theorem oldNode354 (p : Pattern) : eval read p 5046753 = NetHack.Sokoban12CostPartition.d354 p := by
  change eval read p 5046753 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d353 p)
  have code : read 5046753 = .branch 133 4981413 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode353 p, oldNode66 p]
theorem oldNode355 (p : Pattern) : eval read p 5112168 = NetHack.Sokoban12CostPartition.d355 p := by
  change eval read p 5112168 = (if p 132 then NetHack.Sokoban12CostPartition.d354 p else NetHack.Sokoban12CostPartition.d352 p)
  have code : read 5112168 = .branch 132 5046752 5046753 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode352 p, oldNode354 p]
theorem oldNode356 (p : Pattern) : eval read p 5439694 = NetHack.Sokoban12CostPartition.d356 p := by
  change eval read p 5439694 = (if p 108 then NetHack.Sokoban12CostPartition.d355 p else NetHack.Sokoban12CostPartition.d344 p)
  have code : read 5439694 = .branch 108 5112167 5112168 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode344 p, oldNode355 p]
theorem oldNode366 (p : Pattern) : eval read p 5046754 = NetHack.Sokoban12CostPartition.d366 p := by
  change eval read p 5046754 = (if p 133 then NetHack.Sokoban12CostPartition.d231 p else NetHack.Sokoban12CostPartition.d227 p)
  have code : read 5046754 = .branch 133 4784977 4784978 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode227 p, oldNode231 p]
theorem oldNode367 (p : Pattern) : eval read p 5046755 = NetHack.Sokoban12CostPartition.d367 p := by
  change eval read p 5046755 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d231 p)
  have code : read 5046755 = .branch 133 4784978 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode231 p, oldNode66 p]
theorem oldNode368 (p : Pattern) : eval read p 5112169 = NetHack.Sokoban12CostPartition.d368 p := by
  change eval read p 5112169 = (if p 132 then NetHack.Sokoban12CostPartition.d367 p else NetHack.Sokoban12CostPartition.d366 p)
  have code : read 5112169 = .branch 132 5046754 5046755 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode366 p, oldNode367 p]
theorem oldNode369 (p : Pattern) : eval read p 4981414 = NetHack.Sokoban12CostPartition.d369 p := by
  change eval read p 4981414 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d227 p)
  have code : read 4981414 = .branch 134 4784977 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode227 p, oldNode66 p]
theorem oldNode370 (p : Pattern) : eval read p 4981415 = NetHack.Sokoban12CostPartition.d370 p := by
  change eval read p 4981415 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d231 p)
  have code : read 4981415 = .branch 134 4784978 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode231 p, oldNode66 p]
theorem oldNode371 (p : Pattern) : eval read p 5046756 = NetHack.Sokoban12CostPartition.d371 p := by
  change eval read p 5046756 = (if p 133 then NetHack.Sokoban12CostPartition.d370 p else NetHack.Sokoban12CostPartition.d369 p)
  have code : read 5046756 = .branch 133 4981414 4981415 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode369 p, oldNode370 p]
theorem oldNode372 (p : Pattern) : eval read p 5046757 = NetHack.Sokoban12CostPartition.d372 p := by
  change eval read p 5046757 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d370 p)
  have code : read 5046757 = .branch 133 4981415 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode370 p, oldNode66 p]
end NetHack.Soko12Forward220.Shared
