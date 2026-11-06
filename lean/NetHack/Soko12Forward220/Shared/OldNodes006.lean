import NetHack.Soko12Forward220.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward220.Shared.OldNodes005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode217 (p : Pattern) : eval read p 5046737 = NetHack.Sokoban12CostPartition.d217 p := by
  change eval read p 5046737 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 5046737 = .branch 133 4981385 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode66 p]
theorem oldNode218 (p : Pattern) : eval read p 5112159 = NetHack.Sokoban12CostPartition.d218 p := by
  change eval read p 5112159 = (if p 132 then NetHack.Sokoban12CostPartition.d73 p else NetHack.Sokoban12CostPartition.d217 p)
  have code : read 5112159 = .branch 132 5046737 5046726 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode217 p, oldNode73 p]
theorem oldNode219 (p : Pattern) : eval read p 5439689 = NetHack.Sokoban12CostPartition.d219 p := by
  change eval read p 5439689 = (if p 108 then NetHack.Sokoban12CostPartition.d218 p else NetHack.Sokoban12CostPartition.d216 p)
  have code : read 5439689 = .branch 108 5112158 5112159 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode216 p, oldNode218 p]
theorem oldNode227 (p : Pattern) : eval read p 4784977 = NetHack.Sokoban12CostPartition.d227 p := by
  change eval read p 4784977 = (if p 141 then NetHack.Sokoban12CostPartition.d109 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4784977 = .branch 141 4391983 4391984 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode109 p]
theorem oldNode228 (p : Pattern) : eval read p 4981397 = NetHack.Sokoban12CostPartition.d228 p := by
  change eval read p 4981397 = (if p 134 then NetHack.Sokoban12CostPartition.d227 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 4981397 = .branch 134 4784968 4784977 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode227 p]
theorem oldNode229 (p : Pattern) : eval read p 4523379 = NetHack.Sokoban12CostPartition.d229 p := by
  change eval read p 4523379 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 4523379 = .branch 158 4391983 3411913 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode55 p]
theorem oldNode230 (p : Pattern) : eval read p 4523380 = NetHack.Sokoban12CostPartition.d230 p := by
  change eval read p 4523380 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 4523380 = .branch 158 4391984 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode65 p]
theorem oldNode231 (p : Pattern) : eval read p 4784978 = NetHack.Sokoban12CostPartition.d231 p := by
  change eval read p 4784978 = (if p 141 then NetHack.Sokoban12CostPartition.d230 p else NetHack.Sokoban12CostPartition.d229 p)
  have code : read 4784978 = .branch 141 4523379 4523380 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode229 p, oldNode230 p]
theorem oldNode232 (p : Pattern) : eval read p 4981398 = NetHack.Sokoban12CostPartition.d232 p := by
  change eval read p 4981398 = (if p 134 then NetHack.Sokoban12CostPartition.d231 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 4981398 = .branch 134 4784970 4784978 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode231 p]
theorem oldNode233 (p : Pattern) : eval read p 5046738 = NetHack.Sokoban12CostPartition.d233 p := by
  change eval read p 5046738 = (if p 133 then NetHack.Sokoban12CostPartition.d232 p else NetHack.Sokoban12CostPartition.d228 p)
  have code : read 5046738 = .branch 133 4981397 4981398 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode228 p, oldNode232 p]
theorem oldNode234 (p : Pattern) : eval read p 5046739 = NetHack.Sokoban12CostPartition.d234 p := by
  change eval read p 5046739 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d232 p)
  have code : read 5046739 = .branch 133 4981398 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode232 p, oldNode66 p]
theorem oldNode235 (p : Pattern) : eval read p 5112160 = NetHack.Sokoban12CostPartition.d235 p := by
  change eval read p 5112160 = (if p 132 then NetHack.Sokoban12CostPartition.d234 p else NetHack.Sokoban12CostPartition.d233 p)
  have code : read 5112160 = .branch 132 5046738 5046739 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode233 p, oldNode234 p]
theorem oldNode236 (p : Pattern) : eval read p 5439690 = NetHack.Sokoban12CostPartition.d236 p := by
  change eval read p 5439690 = (if p 108 then NetHack.Sokoban12CostPartition.d74 p else NetHack.Sokoban12CostPartition.d235 p)
  have code : read 5439690 = .branch 108 5112160 5112151 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode235 p, oldNode74 p]
theorem oldNode237 (p : Pattern) : eval read p 4523381 = NetHack.Sokoban12CostPartition.d237 p := by
  change eval read p 4523381 = (if p 158 then NetHack.Sokoban12CostPartition.d129 p else NetHack.Sokoban12CostPartition.d109 p)
  have code : read 4523381 = .branch 158 4391984 4457757 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode109 p, oldNode129 p]
theorem oldNode238 (p : Pattern) : eval read p 4784979 = NetHack.Sokoban12CostPartition.d238 p := by
  change eval read p 4784979 = (if p 141 then NetHack.Sokoban12CostPartition.d237 p else NetHack.Sokoban12CostPartition.d179 p)
  have code : read 4784979 = .branch 141 4523372 4523381 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode179 p, oldNode237 p]
theorem oldNode239 (p : Pattern) : eval read p 4981399 = NetHack.Sokoban12CostPartition.d239 p := by
  change eval read p 4981399 = (if p 134 then NetHack.Sokoban12CostPartition.d238 p else NetHack.Sokoban12CostPartition.d64 p)
  have code : read 4981399 = .branch 134 4784968 4784979 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode64 p, oldNode238 p]
theorem oldNode240 (p : Pattern) : eval read p 4523382 = NetHack.Sokoban12CostPartition.d240 p := by
  change eval read p 4523382 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d129 p)
  have code : read 4523382 = .branch 158 4457757 3999609 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode129 p, oldNode65 p]
theorem oldNode241 (p : Pattern) : eval read p 4784980 = NetHack.Sokoban12CostPartition.d241 p := by
  change eval read p 4784980 = (if p 141 then NetHack.Sokoban12CostPartition.d240 p else NetHack.Sokoban12CostPartition.d181 p)
  have code : read 4784980 = .branch 141 4523373 4523382 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode181 p, oldNode240 p]
theorem oldNode242 (p : Pattern) : eval read p 4981400 = NetHack.Sokoban12CostPartition.d242 p := by
  change eval read p 4981400 = (if p 134 then NetHack.Sokoban12CostPartition.d241 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 4981400 = .branch 134 4784970 4784980 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode241 p]
theorem oldNode243 (p : Pattern) : eval read p 5046740 = NetHack.Sokoban12CostPartition.d243 p := by
  change eval read p 5046740 = (if p 133 then NetHack.Sokoban12CostPartition.d242 p else NetHack.Sokoban12CostPartition.d239 p)
  have code : read 5046740 = .branch 133 4981399 4981400 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode239 p, oldNode242 p]
theorem oldNode244 (p : Pattern) : eval read p 5046741 = NetHack.Sokoban12CostPartition.d244 p := by
  change eval read p 5046741 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d242 p)
  have code : read 5046741 = .branch 133 4981400 4784969 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode242 p, oldNode66 p]
theorem oldNode245 (p : Pattern) : eval read p 5112161 = NetHack.Sokoban12CostPartition.d245 p := by
  change eval read p 5112161 = (if p 132 then NetHack.Sokoban12CostPartition.d244 p else NetHack.Sokoban12CostPartition.d243 p)
  have code : read 5112161 = .branch 132 5046740 5046741 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode243 p, oldNode244 p]
theorem oldNode246 (p : Pattern) : eval read p 4523383 = NetHack.Sokoban12CostPartition.d246 p := by
  change eval read p 4523383 = (if p 158 then NetHack.Sokoban12CostPartition.d155 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 4523383 = .branch 158 4391982 4457764 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode155 p]
theorem oldNode247 (p : Pattern) : eval read p 4784981 = NetHack.Sokoban12CostPartition.d247 p := by
  change eval read p 4784981 = (if p 141 then NetHack.Sokoban12CostPartition.d246 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 4784981 = .branch 141 4523374 4523383 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode246 p]
end NetHack.Soko12Forward220.Shared
