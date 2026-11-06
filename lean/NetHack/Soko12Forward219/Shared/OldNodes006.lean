import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode217 (p : Pattern) : eval read p 376857 = NetHack.Sokoban12CostPartition.d217 p := by
  change eval read p 376857 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 376857 = .branch 133 368642 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode66 p]
theorem oldNode218 (p : Pattern) : eval read p 385041 = NetHack.Sokoban12CostPartition.d218 p := by
  change eval read p 385041 = (if p 132 then NetHack.Sokoban12CostPartition.d73 p else NetHack.Sokoban12CostPartition.d217 p)
  have code : read 385041 = .branch 132 376857 376835 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode217 p, oldNode73 p]
theorem oldNode219 (p : Pattern) : eval read p 409609 = NetHack.Sokoban12CostPartition.d219 p := by
  change eval read p 409609 = (if p 108 then NetHack.Sokoban12CostPartition.d218 p else NetHack.Sokoban12CostPartition.d216 p)
  have code : read 409609 = .branch 108 385040 385041 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode216 p, oldNode218 p]
theorem oldNode227 (p : Pattern) : eval read p 360463 = NetHack.Sokoban12CostPartition.d227 p := by
  change eval read p 360463 = (if p 141 then NetHack.Sokoban12CostPartition.d109 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 360463 = .branch 141 319495 319496 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode109 p]
theorem oldNode228 (p : Pattern) : eval read p 368666 = NetHack.Sokoban12CostPartition.d228 p := by
  change eval read p 368666 = (if p 134 then NetHack.Sokoban12CostPartition.d227 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 368666 = .branch 134 360454 360463 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode227 p]
theorem oldNode229 (p : Pattern) : eval read p 335904 = NetHack.Sokoban12CostPartition.d229 p := by
  change eval read p 335904 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 335904 = .branch 158 319495 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode55 p]
theorem oldNode230 (p : Pattern) : eval read p 335905 = NetHack.Sokoban12CostPartition.d230 p := by
  change eval read p 335905 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 335905 = .branch 158 319496 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode65 p]
theorem oldNode231 (p : Pattern) : eval read p 360464 = NetHack.Sokoban12CostPartition.d231 p := by
  change eval read p 360464 = (if p 141 then NetHack.Sokoban12CostPartition.d230 p else NetHack.Sokoban12CostPartition.d229 p)
  have code : read 360464 = .branch 141 335904 335905 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode229 p, oldNode230 p]
theorem oldNode232 (p : Pattern) : eval read p 368667 = NetHack.Sokoban12CostPartition.d232 p := by
  change eval read p 368667 = (if p 134 then NetHack.Sokoban12CostPartition.d231 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 368667 = .branch 134 360456 360464 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode231 p]
theorem oldNode233 (p : Pattern) : eval read p 376860 = NetHack.Sokoban12CostPartition.d233 p := by
  change eval read p 376860 = (if p 133 then NetHack.Sokoban12CostPartition.d232 p else NetHack.Sokoban12CostPartition.d228 p)
  have code : read 376860 = .branch 133 368666 368667 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode228 p, oldNode232 p]
theorem oldNode234 (p : Pattern) : eval read p 376861 = NetHack.Sokoban12CostPartition.d234 p := by
  change eval read p 376861 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d232 p)
  have code : read 376861 = .branch 133 368667 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode232 p, oldNode66 p]
theorem oldNode235 (p : Pattern) : eval read p 385043 = NetHack.Sokoban12CostPartition.d235 p := by
  change eval read p 385043 = (if p 132 then NetHack.Sokoban12CostPartition.d234 p else NetHack.Sokoban12CostPartition.d233 p)
  have code : read 385043 = .branch 132 376860 376861 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode233 p, oldNode234 p]
theorem oldNode236 (p : Pattern) : eval read p 409611 = NetHack.Sokoban12CostPartition.d236 p := by
  change eval read p 409611 = (if p 108 then NetHack.Sokoban12CostPartition.d74 p else NetHack.Sokoban12CostPartition.d235 p)
  have code : read 409611 = .branch 108 385043 385025 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode235 p, oldNode74 p]
theorem oldNode237 (p : Pattern) : eval read p 335906 = NetHack.Sokoban12CostPartition.d237 p := by
  change eval read p 335906 = (if p 158 then NetHack.Sokoban12CostPartition.d129 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 335906 = .branch 158 319496 327693 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode129 p]
theorem oldNode238 (p : Pattern) : eval read p 360465 = NetHack.Sokoban12CostPartition.d238 p := by
  change eval read p 360465 = (if p 141 then NetHack.Sokoban12CostPartition.d237 p else NetHack.Sokoban12CostPartition.d179 p)
  have code : read 360465 = .branch 141 335895 335906 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode179 p, oldNode237 p]
theorem oldNode239 (p : Pattern) : eval read p 368668 = NetHack.Sokoban12CostPartition.d239 p := by
  change eval read p 368668 = (if p 134 then NetHack.Sokoban12CostPartition.d238 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 368668 = .branch 134 360454 360465 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode238 p]
theorem oldNode240 (p : Pattern) : eval read p 335907 = NetHack.Sokoban12CostPartition.d240 p := by
  change eval read p 335907 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d129 p)
  have code : read 335907 = .branch 158 327693 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode129 p, oldNode65 p]
theorem oldNode241 (p : Pattern) : eval read p 360466 = NetHack.Sokoban12CostPartition.d241 p := by
  change eval read p 360466 = (if p 141 then NetHack.Sokoban12CostPartition.d240 p else NetHack.Sokoban12CostPartition.d181 p)
  have code : read 360466 = .branch 141 335896 335907 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode181 p, oldNode240 p]
theorem oldNode242 (p : Pattern) : eval read p 368669 = NetHack.Sokoban12CostPartition.d242 p := by
  change eval read p 368669 = (if p 134 then NetHack.Sokoban12CostPartition.d241 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 368669 = .branch 134 360456 360466 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode241 p]
theorem oldNode243 (p : Pattern) : eval read p 376862 = NetHack.Sokoban12CostPartition.d243 p := by
  change eval read p 376862 = (if p 133 then NetHack.Sokoban12CostPartition.d242 p else NetHack.Sokoban12CostPartition.d239 p)
  have code : read 376862 = .branch 133 368668 368669 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode239 p, oldNode242 p]
theorem oldNode244 (p : Pattern) : eval read p 376863 = NetHack.Sokoban12CostPartition.d244 p := by
  change eval read p 376863 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d242 p)
  have code : read 376863 = .branch 133 368669 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode242 p, oldNode66 p]
theorem oldNode245 (p : Pattern) : eval read p 385044 = NetHack.Sokoban12CostPartition.d245 p := by
  change eval read p 385044 = (if p 132 then NetHack.Sokoban12CostPartition.d244 p else NetHack.Sokoban12CostPartition.d243 p)
  have code : read 385044 = .branch 132 376862 376863 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode243 p, oldNode244 p]
theorem oldNode246 (p : Pattern) : eval read p 335908 = NetHack.Sokoban12CostPartition.d246 p := by
  change eval read p 335908 = (if p 158 then NetHack.Sokoban12CostPartition.d155 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 335908 = .branch 158 319490 327700 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode155 p]
theorem oldNode247 (p : Pattern) : eval read p 360467 = NetHack.Sokoban12CostPartition.d247 p := by
  change eval read p 360467 = (if p 141 then NetHack.Sokoban12CostPartition.d246 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 360467 = .branch 141 335897 335908 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode246 p]
end NetHack.Soko12Forward219.Shared
