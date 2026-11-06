import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode696 (p : Pattern) : eval read p 360519 = NetHack.Sokoban12CostPartition.d696 p := by
  change eval read p 360519 = (if p 141 then NetHack.Sokoban12CostPartition.d695 p else NetHack.Sokoban12CostPartition.d694 p)
  have code : read 360519 = .branch 141 335982 335983 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode694 p, oldNode695 p]
theorem oldNode697 (p : Pattern) : eval read p 335984 = NetHack.Sokoban12CostPartition.d697 p := by
  change eval read p 335984 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d682 p)
  have code : read 335984 = .branch 158 327728 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode682 p, oldNode674 p]
theorem oldNode698 (p : Pattern) : eval read p 335985 = NetHack.Sokoban12CostPartition.d698 p := by
  change eval read p 335985 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d690 p)
  have code : read 335985 = .branch 158 327729 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode690 p, oldNode684 p]
theorem oldNode699 (p : Pattern) : eval read p 360520 = NetHack.Sokoban12CostPartition.d699 p := by
  change eval read p 360520 = (if p 141 then NetHack.Sokoban12CostPartition.d698 p else NetHack.Sokoban12CostPartition.d697 p)
  have code : read 360520 = .branch 141 335984 335985 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode697 p, oldNode698 p]
theorem oldNode700 (p : Pattern) : eval read p 368726 = NetHack.Sokoban12CostPartition.d700 p := by
  change eval read p 368726 = (if p 134 then NetHack.Sokoban12CostPartition.d699 p else NetHack.Sokoban12CostPartition.d696 p)
  have code : read 368726 = .branch 134 360519 360520 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode696 p, oldNode699 p]
theorem oldNode701 (p : Pattern) : eval read p 376918 = NetHack.Sokoban12CostPartition.d701 p := by
  change eval read p 376918 = (if p 133 then NetHack.Sokoban12CostPartition.d700 p else NetHack.Sokoban12CostPartition.d693 p)
  have code : read 376918 = .branch 133 368725 368726 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode693 p, oldNode700 p]
theorem oldNode702 (p : Pattern) : eval read p 360521 = NetHack.Sokoban12CostPartition.d702 p := by
  change eval read p 360521 = (if p 141 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d674 p)
  have code : read 360521 = .branch 141 286760 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode674 p, oldNode684 p]
theorem oldNode703 (p : Pattern) : eval read p 376919 = NetHack.Sokoban12CostPartition.d703 p := by
  change eval read p 376919 = (if p 133 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d700 p)
  have code : read 376919 = .branch 133 368726 360521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode700 p, oldNode702 p]
theorem oldNode704 (p : Pattern) : eval read p 385074 = NetHack.Sokoban12CostPartition.d704 p := by
  change eval read p 385074 = (if p 132 then NetHack.Sokoban12CostPartition.d703 p else NetHack.Sokoban12CostPartition.d701 p)
  have code : read 385074 = .branch 132 376918 376919 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode701 p, oldNode703 p]
theorem oldNode705 (p : Pattern) : eval read p 270372 = NetHack.Sokoban12CostPartition.d705 p := by
  change eval read p 270372 = (if p 186 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d676 p)
  have code : read 270372 = .branch 186 262154 229395 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode676 p, oldNode662 p]
theorem oldNode706 (p : Pattern) : eval read p 270373 = NetHack.Sokoban12CostPartition.d706 p := by
  change eval read p 270373 = (if p 186 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d678 p)
  have code : read 270373 = .branch 186 262155 229396 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode678 p, oldNode665 p]
theorem oldNode707 (p : Pattern) : eval read p 286764 = NetHack.Sokoban12CostPartition.d707 p := by
  change eval read p 286764 = (if p 168 then NetHack.Sokoban12CostPartition.d706 p else NetHack.Sokoban12CostPartition.d705 p)
  have code : read 286764 = .branch 168 270372 270373 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode705 p, oldNode706 p]
theorem oldNode708 (p : Pattern) : eval read p 319556 = NetHack.Sokoban12CostPartition.d708 p := by
  change eval read p 319556 = (if p 160 then NetHack.Sokoban12CostPartition.d707 p else NetHack.Sokoban12CostPartition.d680 p)
  have code : read 319556 = .branch 160 286761 286764 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode680 p, oldNode707 p]
theorem oldNode709 (p : Pattern) : eval read p 327730 = NetHack.Sokoban12CostPartition.d709 p := by
  change eval read p 327730 = (if p 159 then NetHack.Sokoban12CostPartition.d708 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 327730 = .branch 159 319550 319556 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode708 p]
theorem oldNode710 (p : Pattern) : eval read p 335986 = NetHack.Sokoban12CostPartition.d710 p := by
  change eval read p 335986 = (if p 158 then NetHack.Sokoban12CostPartition.d709 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 335986 = .branch 158 319550 327730 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode709 p]
theorem oldNode711 (p : Pattern) : eval read p 270374 = NetHack.Sokoban12CostPartition.d711 p := by
  change eval read p 270374 = (if p 186 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d686 p)
  have code : read 270374 = .branch 186 262156 229397 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode686 p, oldNode669 p]
theorem oldNode712 (p : Pattern) : eval read p 286765 = NetHack.Sokoban12CostPartition.d712 p := by
  change eval read p 286765 = (if p 168 then NetHack.Sokoban12CostPartition.d711 p else NetHack.Sokoban12CostPartition.d706 p)
  have code : read 286765 = .branch 168 270373 270374 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode706 p, oldNode711 p]
theorem oldNode713 (p : Pattern) : eval read p 319557 = NetHack.Sokoban12CostPartition.d713 p := by
  change eval read p 319557 = (if p 160 then NetHack.Sokoban12CostPartition.d712 p else NetHack.Sokoban12CostPartition.d688 p)
  have code : read 319557 = .branch 160 286763 286765 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode688 p, oldNode712 p]
theorem oldNode714 (p : Pattern) : eval read p 327731 = NetHack.Sokoban12CostPartition.d714 p := by
  change eval read p 327731 = (if p 159 then NetHack.Sokoban12CostPartition.d713 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 327731 = .branch 159 319551 319557 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode713 p]
theorem oldNode715 (p : Pattern) : eval read p 335987 = NetHack.Sokoban12CostPartition.d715 p := by
  change eval read p 335987 = (if p 158 then NetHack.Sokoban12CostPartition.d714 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 335987 = .branch 158 319551 327731 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode714 p]
theorem oldNode716 (p : Pattern) : eval read p 360522 = NetHack.Sokoban12CostPartition.d716 p := by
  change eval read p 360522 = (if p 141 then NetHack.Sokoban12CostPartition.d715 p else NetHack.Sokoban12CostPartition.d710 p)
  have code : read 360522 = .branch 141 335986 335987 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode710 p, oldNode715 p]
theorem oldNode717 (p : Pattern) : eval read p 368727 = NetHack.Sokoban12CostPartition.d717 p := by
  change eval read p 368727 = (if p 134 then NetHack.Sokoban12CostPartition.d702 p else NetHack.Sokoban12CostPartition.d716 p)
  have code : read 368727 = .branch 134 360522 360521 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode716 p, oldNode702 p]
theorem oldNode718 (p : Pattern) : eval read p 319558 = NetHack.Sokoban12CostPartition.d718 p := by
  change eval read p 319558 = (if p 160 then NetHack.Sokoban12CostPartition.d707 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 319558 = .branch 160 286727 286764 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode707 p]
theorem oldNode719 (p : Pattern) : eval read p 327732 = NetHack.Sokoban12CostPartition.d719 p := by
  change eval read p 327732 = (if p 159 then NetHack.Sokoban12CostPartition.d708 p else NetHack.Sokoban12CostPartition.d718 p)
  have code : read 327732 = .branch 159 319558 319556 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode718 p, oldNode708 p]
end NetHack.Soko12Forward219.Shared
