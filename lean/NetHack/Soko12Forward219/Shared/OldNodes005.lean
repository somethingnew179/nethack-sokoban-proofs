import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode182 (p : Pattern) : eval read p 368658 = NetHack.Sokoban12CostPartition.d182 p := by
  change eval read p 368658 = (if p 134 then NetHack.Sokoban12CostPartition.d181 p else NetHack.Sokoban12CostPartition.d68 p)
  have code : read 368658 = .branch 134 335873 335896 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode68 p, oldNode181 p]
theorem oldNode183 (p : Pattern) : eval read p 376848 = NetHack.Sokoban12CostPartition.d183 p := by
  change eval read p 376848 = (if p 133 then NetHack.Sokoban12CostPartition.d182 p else NetHack.Sokoban12CostPartition.d180 p)
  have code : read 376848 = .branch 133 368657 368658 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode180 p, oldNode182 p]
theorem oldNode184 (p : Pattern) : eval read p 376849 = NetHack.Sokoban12CostPartition.d184 p := by
  change eval read p 376849 = (if p 133 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d182 p)
  have code : read 376849 = .branch 133 368658 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode182 p, oldNode55 p]
theorem oldNode185 (p : Pattern) : eval read p 385032 = NetHack.Sokoban12CostPartition.d185 p := by
  change eval read p 385032 = (if p 132 then NetHack.Sokoban12CostPartition.d184 p else NetHack.Sokoban12CostPartition.d183 p)
  have code : read 385032 = .branch 132 376848 376849 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode183 p, oldNode184 p]
theorem oldNode186 (p : Pattern) : eval read p 335897 = NetHack.Sokoban12CostPartition.d186 p := by
  change eval read p 335897 = (if p 158 then NetHack.Sokoban12CostPartition.d153 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 335897 = .branch 158 319489 327699 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode153 p]
theorem oldNode187 (p : Pattern) : eval read p 368659 = NetHack.Sokoban12CostPartition.d187 p := by
  change eval read p 368659 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d186 p)
  have code : read 368659 = .branch 134 335897 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode186 p, oldNode55 p]
theorem oldNode188 (p : Pattern) : eval read p 335898 = NetHack.Sokoban12CostPartition.d188 p := by
  change eval read p 335898 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d140 p)
  have code : read 335898 = .branch 158 327695 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode140 p, oldNode55 p]
theorem oldNode189 (p : Pattern) : eval read p 368660 = NetHack.Sokoban12CostPartition.d189 p := by
  change eval read p 368660 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d188 p)
  have code : read 368660 = .branch 134 335898 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode188 p, oldNode55 p]
theorem oldNode190 (p : Pattern) : eval read p 376850 = NetHack.Sokoban12CostPartition.d190 p := by
  change eval read p 376850 = (if p 133 then NetHack.Sokoban12CostPartition.d189 p else NetHack.Sokoban12CostPartition.d187 p)
  have code : read 376850 = .branch 133 368659 368660 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode187 p, oldNode189 p]
theorem oldNode191 (p : Pattern) : eval read p 335899 = NetHack.Sokoban12CostPartition.d191 p := by
  change eval read p 335899 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d153 p)
  have code : read 335899 = .branch 158 327699 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode153 p, oldNode55 p]
theorem oldNode192 (p : Pattern) : eval read p 368661 = NetHack.Sokoban12CostPartition.d192 p := by
  change eval read p 368661 = (if p 134 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d191 p)
  have code : read 368661 = .branch 134 335899 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode191 p, oldNode55 p]
theorem oldNode193 (p : Pattern) : eval read p 376851 = NetHack.Sokoban12CostPartition.d193 p := by
  change eval read p 376851 = (if p 133 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d192 p)
  have code : read 376851 = .branch 133 368661 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode192 p, oldNode55 p]
theorem oldNode194 (p : Pattern) : eval read p 385033 = NetHack.Sokoban12CostPartition.d194 p := by
  change eval read p 385033 = (if p 132 then NetHack.Sokoban12CostPartition.d193 p else NetHack.Sokoban12CostPartition.d190 p)
  have code : read 385033 = .branch 132 376850 376851 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode190 p, oldNode193 p]
theorem oldNode195 (p : Pattern) : eval read p 409605 = NetHack.Sokoban12CostPartition.d195 p := by
  change eval read p 409605 = (if p 108 then NetHack.Sokoban12CostPartition.d194 p else NetHack.Sokoban12CostPartition.d185 p)
  have code : read 409605 = .branch 108 385032 385033 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode185 p, oldNode194 p]
theorem oldNode199 (p : Pattern) : eval read p 385036 = NetHack.Sokoban12CostPartition.d199 p := by
  change eval read p 385036 = (if p 132 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d134 p)
  have code : read 385036 = .branch 132 376840 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode134 p, oldNode66 p]
theorem oldNode200 (p : Pattern) : eval read p 385037 = NetHack.Sokoban12CostPartition.d200 p := by
  change eval read p 385037 = (if p 132 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d152 p)
  have code : read 385037 = .branch 132 376842 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode152 p, oldNode66 p]
theorem oldNode201 (p : Pattern) : eval read p 409607 = NetHack.Sokoban12CostPartition.d201 p := by
  change eval read p 409607 = (if p 108 then NetHack.Sokoban12CostPartition.d200 p else NetHack.Sokoban12CostPartition.d199 p)
  have code : read 409607 = .branch 108 385036 385037 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode199 p, oldNode200 p]
theorem oldNode210 (p : Pattern) : eval read p 376855 = NetHack.Sokoban12CostPartition.d210 p := by
  change eval read p 376855 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d113 p)
  have code : read 376855 = .branch 133 368648 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode113 p, oldNode66 p]
theorem oldNode211 (p : Pattern) : eval read p 335901 = NetHack.Sokoban12CostPartition.d211 p := by
  change eval read p 335901 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d107 p)
  have code : read 335901 = .branch 158 327687 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode107 p, oldNode55 p]
theorem oldNode212 (p : Pattern) : eval read p 335902 = NetHack.Sokoban12CostPartition.d212 p := by
  change eval read p 335902 = (if p 158 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d110 p)
  have code : read 335902 = .branch 158 327688 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode110 p, oldNode65 p]
theorem oldNode213 (p : Pattern) : eval read p 360462 = NetHack.Sokoban12CostPartition.d213 p := by
  change eval read p 360462 = (if p 141 then NetHack.Sokoban12CostPartition.d212 p else NetHack.Sokoban12CostPartition.d211 p)
  have code : read 360462 = .branch 141 335901 335902 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode211 p, oldNode212 p]
theorem oldNode214 (p : Pattern) : eval read p 368663 = NetHack.Sokoban12CostPartition.d214 p := by
  change eval read p 368663 = (if p 134 then NetHack.Sokoban12CostPartition.d213 p else NetHack.Sokoban12CostPartition.d70 p)
  have code : read 368663 = .branch 134 360456 360462 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode70 p, oldNode213 p]
theorem oldNode215 (p : Pattern) : eval read p 376856 = NetHack.Sokoban12CostPartition.d215 p := by
  change eval read p 376856 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d214 p)
  have code : read 376856 = .branch 133 368663 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode214 p, oldNode66 p]
theorem oldNode216 (p : Pattern) : eval read p 385040 = NetHack.Sokoban12CostPartition.d216 p := by
  change eval read p 385040 = (if p 132 then NetHack.Sokoban12CostPartition.d215 p else NetHack.Sokoban12CostPartition.d210 p)
  have code : read 385040 = .branch 132 376855 376856 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode210 p, oldNode215 p]
end NetHack.Soko12Forward219.Shared
