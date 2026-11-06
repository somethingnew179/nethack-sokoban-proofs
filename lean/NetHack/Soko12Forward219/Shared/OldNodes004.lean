import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode141 (p : Pattern) : eval read p 327696 = NetHack.Sokoban12CostPartition.d141 p := by
  change eval read p 327696 = (if p 159 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d139 p)
  have code : read 327696 = .branch 159 319500 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode139 p, oldNode55 p]
theorem oldNode142 (p : Pattern) : eval read p 335886 = NetHack.Sokoban12CostPartition.d142 p := by
  change eval read p 335886 = (if p 158 then NetHack.Sokoban12CostPartition.d141 p else NetHack.Sokoban12CostPartition.d140 p)
  have code : read 335886 = .branch 158 327695 327696 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode140 p, oldNode141 p]
theorem oldNode143 (p : Pattern) : eval read p 270344 = NetHack.Sokoban12CostPartition.d143 p := by
  change eval read p 270344 = (if p 186 then NetHack.Sokoban12CostPartition.d60 p else NetHack.Sokoban12CostPartition.d125 p)
  have code : read 270344 = .branch 186 262146 229388 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode125 p, oldNode60 p]
theorem oldNode144 (p : Pattern) : eval read p 286732 = NetHack.Sokoban12CostPartition.d144 p := by
  change eval read p 286732 = (if p 168 then NetHack.Sokoban12CostPartition.d143 p else NetHack.Sokoban12CostPartition.d137 p)
  have code : read 286732 = .branch 168 270343 270344 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode137 p, oldNode143 p]
theorem oldNode145 (p : Pattern) : eval read p 319501 = NetHack.Sokoban12CostPartition.d145 p := by
  change eval read p 319501 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d12 p)
  have code : read 319501 = .branch 160 286720 286732 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode12 p, oldNode144 p]
theorem oldNode146 (p : Pattern) : eval read p 319502 = NetHack.Sokoban12CostPartition.d146 p := by
  change eval read p 319502 = (if p 160 then NetHack.Sokoban12CostPartition.d144 p else NetHack.Sokoban12CostPartition.d127 p)
  have code : read 319502 = .branch 160 286731 286732 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode127 p, oldNode144 p]
theorem oldNode147 (p : Pattern) : eval read p 327697 = NetHack.Sokoban12CostPartition.d147 p := by
  change eval read p 327697 = (if p 159 then NetHack.Sokoban12CostPartition.d146 p else NetHack.Sokoban12CostPartition.d145 p)
  have code : read 327697 = .branch 159 319501 319502 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode145 p, oldNode146 p]
theorem oldNode148 (p : Pattern) : eval read p 327698 = NetHack.Sokoban12CostPartition.d148 p := by
  change eval read p 327698 = (if p 159 then NetHack.Sokoban12CostPartition.d65 p else NetHack.Sokoban12CostPartition.d146 p)
  have code : read 327698 = .branch 159 319502 286730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode146 p, oldNode65 p]
theorem oldNode149 (p : Pattern) : eval read p 335887 = NetHack.Sokoban12CostPartition.d149 p := by
  change eval read p 335887 = (if p 158 then NetHack.Sokoban12CostPartition.d148 p else NetHack.Sokoban12CostPartition.d147 p)
  have code : read 335887 = .branch 158 327697 327698 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode147 p, oldNode148 p]
theorem oldNode150 (p : Pattern) : eval read p 360460 = NetHack.Sokoban12CostPartition.d150 p := by
  change eval read p 360460 = (if p 141 then NetHack.Sokoban12CostPartition.d149 p else NetHack.Sokoban12CostPartition.d142 p)
  have code : read 360460 = .branch 141 335886 335887 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode142 p, oldNode149 p]
theorem oldNode151 (p : Pattern) : eval read p 368650 = NetHack.Sokoban12CostPartition.d151 p := by
  change eval read p 368650 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d150 p)
  have code : read 368650 = .branch 134 360460 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode150 p, oldNode66 p]
theorem oldNode152 (p : Pattern) : eval read p 376842 = NetHack.Sokoban12CostPartition.d152 p := by
  change eval read p 376842 = (if p 133 then NetHack.Sokoban12CostPartition.d151 p else NetHack.Sokoban12CostPartition.d67 p)
  have code : read 376842 = .branch 133 368642 368650 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode67 p, oldNode151 p]
theorem oldNode153 (p : Pattern) : eval read p 327699 = NetHack.Sokoban12CostPartition.d153 p := by
  change eval read p 327699 = (if p 159 then NetHack.Sokoban12CostPartition.d139 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 327699 = .branch 159 319489 319500 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode139 p]
theorem oldNode154 (p : Pattern) : eval read p 335888 = NetHack.Sokoban12CostPartition.d154 p := by
  change eval read p 335888 = (if p 158 then NetHack.Sokoban12CostPartition.d141 p else NetHack.Sokoban12CostPartition.d153 p)
  have code : read 335888 = .branch 158 327699 327696 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode153 p, oldNode141 p]
theorem oldNode155 (p : Pattern) : eval read p 327700 = NetHack.Sokoban12CostPartition.d155 p := by
  change eval read p 327700 = (if p 159 then NetHack.Sokoban12CostPartition.d146 p else NetHack.Sokoban12CostPartition.d63 p)
  have code : read 327700 = .branch 159 319490 319502 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode63 p, oldNode146 p]
theorem oldNode156 (p : Pattern) : eval read p 335889 = NetHack.Sokoban12CostPartition.d156 p := by
  change eval read p 335889 = (if p 158 then NetHack.Sokoban12CostPartition.d148 p else NetHack.Sokoban12CostPartition.d155 p)
  have code : read 335889 = .branch 158 327700 327698 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode155 p, oldNode148 p]
theorem oldNode157 (p : Pattern) : eval read p 360461 = NetHack.Sokoban12CostPartition.d157 p := by
  change eval read p 360461 = (if p 141 then NetHack.Sokoban12CostPartition.d156 p else NetHack.Sokoban12CostPartition.d154 p)
  have code : read 360461 = .branch 141 335888 335889 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode154 p, oldNode156 p]
theorem oldNode158 (p : Pattern) : eval read p 368651 = NetHack.Sokoban12CostPartition.d158 p := by
  change eval read p 368651 = (if p 134 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d157 p)
  have code : read 368651 = .branch 134 360461 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode157 p, oldNode66 p]
theorem oldNode159 (p : Pattern) : eval read p 376843 = NetHack.Sokoban12CostPartition.d159 p := by
  change eval read p 376843 = (if p 133 then NetHack.Sokoban12CostPartition.d66 p else NetHack.Sokoban12CostPartition.d158 p)
  have code : read 376843 = .branch 133 368651 360455 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode158 p, oldNode66 p]
theorem oldNode160 (p : Pattern) : eval read p 385029 = NetHack.Sokoban12CostPartition.d160 p := by
  change eval read p 385029 = (if p 132 then NetHack.Sokoban12CostPartition.d159 p else NetHack.Sokoban12CostPartition.d152 p)
  have code : read 385029 = .branch 132 376842 376843 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode152 p, oldNode159 p]
theorem oldNode161 (p : Pattern) : eval read p 409603 = NetHack.Sokoban12CostPartition.d161 p := by
  change eval read p 409603 = (if p 108 then NetHack.Sokoban12CostPartition.d160 p else NetHack.Sokoban12CostPartition.d136 p)
  have code : read 409603 = .branch 108 385028 385029 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode136 p, oldNode160 p]
theorem oldNode179 (p : Pattern) : eval read p 335895 = NetHack.Sokoban12CostPartition.d179 p := by
  change eval read p 335895 = (if p 158 then NetHack.Sokoban12CostPartition.d122 p else NetHack.Sokoban12CostPartition.d106 p)
  have code : read 335895 = .branch 158 319495 327691 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode106 p, oldNode122 p]
theorem oldNode180 (p : Pattern) : eval read p 368657 = NetHack.Sokoban12CostPartition.d180 p := by
  change eval read p 368657 = (if p 134 then NetHack.Sokoban12CostPartition.d179 p else NetHack.Sokoban12CostPartition.d57 p)
  have code : read 368657 = .branch 134 319489 335895 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode57 p, oldNode179 p]
theorem oldNode181 (p : Pattern) : eval read p 335896 = NetHack.Sokoban12CostPartition.d181 p := by
  change eval read p 335896 = (if p 158 then NetHack.Sokoban12CostPartition.d55 p else NetHack.Sokoban12CostPartition.d122 p)
  have code : read 335896 = .branch 158 327691 229387 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode122 p, oldNode55 p]
end NetHack.Soko12Forward219.Shared
