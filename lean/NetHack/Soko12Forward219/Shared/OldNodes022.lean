import NetHack.Soko12Forward219.Shared.Facts
import NetHack.Sokoban12CostPartition.Roots
import NetHack.Soko12Forward219.Shared.OldNodes021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban NetHack.Sokoban.DecisionDAG
theorem oldNode672 (p : Pattern) : eval read p 319551 = NetHack.Sokoban12CostPartition.d672 p := by
  change eval read p 319551 = (if p 160 then NetHack.Sokoban12CostPartition.d671 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 319551 = .branch 160 286728 286759 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode671 p]
theorem oldNode673 (p : Pattern) : eval read p 360517 = NetHack.Sokoban12CostPartition.d673 p := by
  change eval read p 360517 = (if p 141 then NetHack.Sokoban12CostPartition.d672 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 360517 = .branch 141 319550 319551 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode672 p]
theorem oldNode674 (p : Pattern) : eval read p 286760 = NetHack.Sokoban12CostPartition.d674 p := by
  change eval read p 286760 = (if p 168 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d662 p)
  have code : read 286760 = .branch 168 229395 229396 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode662 p, oldNode665 p]
theorem oldNode675 (p : Pattern) : eval read p 319552 = NetHack.Sokoban12CostPartition.d675 p := by
  change eval read p 319552 = (if p 160 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d41 p)
  have code : read 319552 = .branch 160 286727 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode41 p, oldNode674 p]
theorem oldNode676 (p : Pattern) : eval read p 262154 = NetHack.Sokoban12CostPartition.d676 p := by
  change eval read p 262154 = (if p 187 then NetHack.Sokoban12CostPartition.d662 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 262154 = .branch 187 229384 229395 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode662 p]
theorem oldNode677 (p : Pattern) : eval read p 270369 = NetHack.Sokoban12CostPartition.d677 p := by
  change eval read p 270369 = (if p 186 then NetHack.Sokoban12CostPartition.d676 p else NetHack.Sokoban12CostPartition.d38 p)
  have code : read 270369 = .branch 186 229384 262154 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode38 p, oldNode676 p]
theorem oldNode678 (p : Pattern) : eval read p 262155 = NetHack.Sokoban12CostPartition.d678 p := by
  change eval read p 262155 = (if p 187 then NetHack.Sokoban12CostPartition.d665 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 262155 = .branch 187 229385 229396 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode665 p]
theorem oldNode679 (p : Pattern) : eval read p 270370 = NetHack.Sokoban12CostPartition.d679 p := by
  change eval read p 270370 = (if p 186 then NetHack.Sokoban12CostPartition.d678 p else NetHack.Sokoban12CostPartition.d40 p)
  have code : read 270370 = .branch 186 229385 262155 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode40 p, oldNode678 p]
theorem oldNode680 (p : Pattern) : eval read p 286761 = NetHack.Sokoban12CostPartition.d680 p := by
  change eval read p 286761 = (if p 168 then NetHack.Sokoban12CostPartition.d679 p else NetHack.Sokoban12CostPartition.d677 p)
  have code : read 286761 = .branch 168 270369 270370 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode677 p, oldNode679 p]
theorem oldNode681 (p : Pattern) : eval read p 319553 = NetHack.Sokoban12CostPartition.d681 p := by
  change eval read p 319553 = (if p 160 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d680 p)
  have code : read 319553 = .branch 160 286761 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode680 p, oldNode674 p]
theorem oldNode682 (p : Pattern) : eval read p 327728 = NetHack.Sokoban12CostPartition.d682 p := by
  change eval read p 327728 = (if p 159 then NetHack.Sokoban12CostPartition.d681 p else NetHack.Sokoban12CostPartition.d675 p)
  have code : read 327728 = .branch 159 319552 319553 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode675 p, oldNode681 p]
theorem oldNode683 (p : Pattern) : eval read p 335980 = NetHack.Sokoban12CostPartition.d683 p := by
  change eval read p 335980 = (if p 158 then NetHack.Sokoban12CostPartition.d682 p else NetHack.Sokoban12CostPartition.d675 p)
  have code : read 335980 = .branch 158 319552 327728 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode675 p, oldNode682 p]
theorem oldNode684 (p : Pattern) : eval read p 286762 = NetHack.Sokoban12CostPartition.d684 p := by
  change eval read p 286762 = (if p 168 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d665 p)
  have code : read 286762 = .branch 168 229396 229397 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode665 p, oldNode669 p]
theorem oldNode685 (p : Pattern) : eval read p 319554 = NetHack.Sokoban12CostPartition.d685 p := by
  change eval read p 319554 = (if p 160 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d43 p)
  have code : read 319554 = .branch 160 286728 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode43 p, oldNode684 p]
theorem oldNode686 (p : Pattern) : eval read p 262156 = NetHack.Sokoban12CostPartition.d686 p := by
  change eval read p 262156 = (if p 187 then NetHack.Sokoban12CostPartition.d669 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 262156 = .branch 187 229386 229397 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode669 p]
theorem oldNode687 (p : Pattern) : eval read p 270371 = NetHack.Sokoban12CostPartition.d687 p := by
  change eval read p 270371 = (if p 186 then NetHack.Sokoban12CostPartition.d686 p else NetHack.Sokoban12CostPartition.d42 p)
  have code : read 270371 = .branch 186 229386 262156 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode42 p, oldNode686 p]
theorem oldNode688 (p : Pattern) : eval read p 286763 = NetHack.Sokoban12CostPartition.d688 p := by
  change eval read p 286763 = (if p 168 then NetHack.Sokoban12CostPartition.d687 p else NetHack.Sokoban12CostPartition.d679 p)
  have code : read 286763 = .branch 168 270370 270371 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode679 p, oldNode687 p]
theorem oldNode689 (p : Pattern) : eval read p 319555 = NetHack.Sokoban12CostPartition.d689 p := by
  change eval read p 319555 = (if p 160 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d688 p)
  have code : read 319555 = .branch 160 286763 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode688 p, oldNode684 p]
theorem oldNode690 (p : Pattern) : eval read p 327729 = NetHack.Sokoban12CostPartition.d690 p := by
  change eval read p 327729 = (if p 159 then NetHack.Sokoban12CostPartition.d689 p else NetHack.Sokoban12CostPartition.d685 p)
  have code : read 327729 = .branch 159 319554 319555 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode685 p, oldNode689 p]
theorem oldNode691 (p : Pattern) : eval read p 335981 = NetHack.Sokoban12CostPartition.d691 p := by
  change eval read p 335981 = (if p 158 then NetHack.Sokoban12CostPartition.d690 p else NetHack.Sokoban12CostPartition.d685 p)
  have code : read 335981 = .branch 158 319554 327729 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode685 p, oldNode690 p]
theorem oldNode692 (p : Pattern) : eval read p 360518 = NetHack.Sokoban12CostPartition.d692 p := by
  change eval read p 360518 = (if p 141 then NetHack.Sokoban12CostPartition.d691 p else NetHack.Sokoban12CostPartition.d683 p)
  have code : read 360518 = .branch 141 335980 335981 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode683 p, oldNode691 p]
theorem oldNode693 (p : Pattern) : eval read p 368725 = NetHack.Sokoban12CostPartition.d693 p := by
  change eval read p 368725 = (if p 134 then NetHack.Sokoban12CostPartition.d692 p else NetHack.Sokoban12CostPartition.d673 p)
  have code : read 368725 = .branch 134 360517 360518 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode673 p, oldNode692 p]
theorem oldNode694 (p : Pattern) : eval read p 335982 = NetHack.Sokoban12CostPartition.d694 p := by
  change eval read p 335982 = (if p 158 then NetHack.Sokoban12CostPartition.d674 p else NetHack.Sokoban12CostPartition.d668 p)
  have code : read 335982 = .branch 158 319550 286760 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode668 p, oldNode674 p]
theorem oldNode695 (p : Pattern) : eval read p 335983 = NetHack.Sokoban12CostPartition.d695 p := by
  change eval read p 335983 = (if p 158 then NetHack.Sokoban12CostPartition.d684 p else NetHack.Sokoban12CostPartition.d672 p)
  have code : read 335983 = .branch 158 319551 286762 := by decide +kernel
  rw [eval_branch code ⟨by decide +kernel, by decide +kernel⟩ p, oldNode672 p, oldNode684 p]
end NetHack.Soko12Forward219.Shared
