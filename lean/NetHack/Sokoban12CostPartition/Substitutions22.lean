/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2640 (p : Pattern) : d671 (change p 271 none) = d56 p := by
  change (if p 168 then d670 (change p 271 none) else d666 (change p 271 none)) = d56 p
  rw [sub2639, sub2633]
  simp only [ite_self]
theorem sub2641 (p : Pattern) : d672 (change p 271 none) = d57 p := by
  change (if p 160 then d671 (change p 271 none) else d43 (change p 271 none)) = d57 p
  rw [sub2640, sub2637]
  rfl
theorem sub2642 (p : Pattern) : d673 (change p 271 none) = d57 p := by
  change (if p 141 then d672 (change p 271 none) else d668 (change p 271 none)) = d57 p
  rw [sub2641, sub2635]
  simp only [ite_self]
theorem sub2643 (p : Pattern) : d674 (change p 271 none) = d55 p := by
  change (if p 168 then d665 (change p 271 none) else d662 (change p 271 none)) = d55 p
  rw [sub2632, sub2629]
  simp only [ite_self]
theorem sub2644 (p : Pattern) : d675 (change p 271 none) = d106 p := by
  change (if p 160 then d674 (change p 271 none) else d41 (change p 271 none)) = d106 p
  rw [sub2643, sub2622]
  rfl
theorem sub2645 (p : Pattern) : d676 (change p 271 none) = d119 p := by
  change (if p 187 then d662 (change p 271 none) else d38 (change p 271 none)) = d119 p
  rw [sub2629, sub2619]
  rfl
theorem sub2646 (p : Pattern) : d677 (change p 271 none) = d120 p := by
  change (if p 186 then d676 (change p 271 none) else d38 (change p 271 none)) = d120 p
  rw [sub2645, sub2619]
  rfl
theorem sub2647 (p : Pattern) : d678 (change p 271 none) = d119 p := by
  change (if p 187 then d665 (change p 271 none) else d40 (change p 271 none)) = d119 p
  rw [sub2632, sub2621]
  rfl
theorem sub2648 (p : Pattern) : d679 (change p 271 none) = d120 p := by
  change (if p 186 then d678 (change p 271 none) else d40 (change p 271 none)) = d120 p
  rw [sub2647, sub2621]
  rfl
theorem sub2649 (p : Pattern) : d680 (change p 271 none) = d120 p := by
  change (if p 168 then d679 (change p 271 none) else d677 (change p 271 none)) = d120 p
  rw [sub2648, sub2646]
  simp only [ite_self]
theorem sub2650 (p : Pattern) : d681 (change p 271 none) = d121 p := by
  change (if p 160 then d674 (change p 271 none) else d680 (change p 271 none)) = d121 p
  rw [sub2643, sub2649]
  rfl
theorem sub2651 (p : Pattern) : d682 (change p 271 none) = d122 p := by
  change (if p 159 then d681 (change p 271 none) else d675 (change p 271 none)) = d122 p
  rw [sub2650, sub2644]
  rfl
theorem sub2652 (p : Pattern) : d683 (change p 271 none) = d179 p := by
  change (if p 158 then d682 (change p 271 none) else d675 (change p 271 none)) = d179 p
  rw [sub2651, sub2644]
  rfl
theorem sub2653 (p : Pattern) : d684 (change p 271 none) = d55 p := by
  change (if p 168 then d669 (change p 271 none) else d665 (change p 271 none)) = d55 p
  rw [sub2638, sub2632]
  simp only [ite_self]
theorem sub2654 (p : Pattern) : d685 (change p 271 none) = d106 p := by
  change (if p 160 then d684 (change p 271 none) else d43 (change p 271 none)) = d106 p
  rw [sub2653, sub2637]
  rfl
theorem sub2655 (p : Pattern) : d686 (change p 271 none) = d119 p := by
  change (if p 187 then d669 (change p 271 none) else d42 (change p 271 none)) = d119 p
  rw [sub2638, sub2636]
  rfl
theorem sub2656 (p : Pattern) : d687 (change p 271 none) = d120 p := by
  change (if p 186 then d686 (change p 271 none) else d42 (change p 271 none)) = d120 p
  rw [sub2655, sub2636]
  rfl
theorem sub2657 (p : Pattern) : d688 (change p 271 none) = d120 p := by
  change (if p 168 then d687 (change p 271 none) else d679 (change p 271 none)) = d120 p
  rw [sub2656, sub2648]
  simp only [ite_self]
theorem sub2658 (p : Pattern) : d689 (change p 271 none) = d121 p := by
  change (if p 160 then d684 (change p 271 none) else d688 (change p 271 none)) = d121 p
  rw [sub2653, sub2657]
  rfl
theorem sub2659 (p : Pattern) : d690 (change p 271 none) = d122 p := by
  change (if p 159 then d689 (change p 271 none) else d685 (change p 271 none)) = d122 p
  rw [sub2658, sub2654]
  rfl
theorem sub2660 (p : Pattern) : d691 (change p 271 none) = d179 p := by
  change (if p 158 then d690 (change p 271 none) else d685 (change p 271 none)) = d179 p
  rw [sub2659, sub2654]
  rfl
theorem sub2661 (p : Pattern) : d692 (change p 271 none) = d179 p := by
  change (if p 141 then d691 (change p 271 none) else d683 (change p 271 none)) = d179 p
  rw [sub2660, sub2652]
  simp only [ite_self]
theorem sub2662 (p : Pattern) : d693 (change p 271 none) = d180 p := by
  change (if p 134 then d692 (change p 271 none) else d673 (change p 271 none)) = d180 p
  rw [sub2661, sub2642]
  rfl
theorem sub2663 (p : Pattern) : d694 (change p 271 none) = d68 p := by
  change (if p 158 then d674 (change p 271 none) else d668 (change p 271 none)) = d68 p
  rw [sub2643, sub2635]
  rfl
theorem sub2664 (p : Pattern) : d695 (change p 271 none) = d68 p := by
  change (if p 158 then d684 (change p 271 none) else d672 (change p 271 none)) = d68 p
  rw [sub2653, sub2641]
  rfl
theorem sub2665 (p : Pattern) : d696 (change p 271 none) = d68 p := by
  change (if p 141 then d695 (change p 271 none) else d694 (change p 271 none)) = d68 p
  rw [sub2664, sub2663]
  simp only [ite_self]
theorem sub2666 (p : Pattern) : d697 (change p 271 none) = d181 p := by
  change (if p 158 then d674 (change p 271 none) else d682 (change p 271 none)) = d181 p
  rw [sub2643, sub2651]
  rfl
theorem sub2667 (p : Pattern) : d698 (change p 271 none) = d181 p := by
  change (if p 158 then d684 (change p 271 none) else d690 (change p 271 none)) = d181 p
  rw [sub2653, sub2659]
  rfl
theorem sub2668 (p : Pattern) : d699 (change p 271 none) = d181 p := by
  change (if p 141 then d698 (change p 271 none) else d697 (change p 271 none)) = d181 p
  rw [sub2667, sub2666]
  simp only [ite_self]
theorem sub2669 (p : Pattern) : d700 (change p 271 none) = d182 p := by
  change (if p 134 then d699 (change p 271 none) else d696 (change p 271 none)) = d182 p
  rw [sub2668, sub2665]
  rfl
theorem sub2670 (p : Pattern) : d701 (change p 271 none) = d183 p := by
  change (if p 133 then d700 (change p 271 none) else d693 (change p 271 none)) = d183 p
  rw [sub2669, sub2662]
  rfl
theorem sub2671 (p : Pattern) : d702 (change p 271 none) = d55 p := by
  change (if p 141 then d684 (change p 271 none) else d674 (change p 271 none)) = d55 p
  rw [sub2653, sub2643]
  simp only [ite_self]
theorem sub2672 (p : Pattern) : d703 (change p 271 none) = d184 p := by
  change (if p 133 then d702 (change p 271 none) else d700 (change p 271 none)) = d184 p
  rw [sub2671, sub2669]
  rfl
theorem sub2673 (p : Pattern) : d704 (change p 271 none) = d185 p := by
  change (if p 132 then d703 (change p 271 none) else d701 (change p 271 none)) = d185 p
  rw [sub2672, sub2670]
  rfl
theorem sub2674 (p : Pattern) : d705 (change p 271 none) = d137 p := by
  change (if p 186 then d662 (change p 271 none) else d676 (change p 271 none)) = d137 p
  rw [sub2629, sub2645]
  rfl
theorem sub2675 (p : Pattern) : d706 (change p 271 none) = d137 p := by
  change (if p 186 then d665 (change p 271 none) else d678 (change p 271 none)) = d137 p
  rw [sub2632, sub2647]
  rfl
theorem sub2676 (p : Pattern) : d707 (change p 271 none) = d137 p := by
  change (if p 168 then d706 (change p 271 none) else d705 (change p 271 none)) = d137 p
  rw [sub2675, sub2674]
  simp only [ite_self]
theorem sub2677 (p : Pattern) : d708 (change p 271 none) = d139 p := by
  change (if p 160 then d707 (change p 271 none) else d680 (change p 271 none)) = d139 p
  rw [sub2676, sub2649]
  rfl
theorem sub2678 (p : Pattern) : d709 (change p 271 none) = d153 p := by
  change (if p 159 then d708 (change p 271 none) else d668 (change p 271 none)) = d153 p
  rw [sub2677, sub2635]
  rfl
theorem sub2679 (p : Pattern) : d710 (change p 271 none) = d186 p := by
  change (if p 158 then d709 (change p 271 none) else d668 (change p 271 none)) = d186 p
  rw [sub2678, sub2635]
  rfl
theorem sub2680 (p : Pattern) : d711 (change p 271 none) = d137 p := by
  change (if p 186 then d669 (change p 271 none) else d686 (change p 271 none)) = d137 p
  rw [sub2638, sub2655]
  rfl
theorem sub2681 (p : Pattern) : d712 (change p 271 none) = d137 p := by
  change (if p 168 then d711 (change p 271 none) else d706 (change p 271 none)) = d137 p
  rw [sub2680, sub2675]
  simp only [ite_self]
theorem sub2682 (p : Pattern) : d713 (change p 271 none) = d139 p := by
  change (if p 160 then d712 (change p 271 none) else d688 (change p 271 none)) = d139 p
  rw [sub2681, sub2657]
  rfl
theorem sub2683 (p : Pattern) : d714 (change p 271 none) = d153 p := by
  change (if p 159 then d713 (change p 271 none) else d672 (change p 271 none)) = d153 p
  rw [sub2682, sub2641]
  rfl
theorem sub2684 (p : Pattern) : d715 (change p 271 none) = d186 p := by
  change (if p 158 then d714 (change p 271 none) else d672 (change p 271 none)) = d186 p
  rw [sub2683, sub2641]
  rfl
theorem sub2685 (p : Pattern) : d716 (change p 271 none) = d186 p := by
  change (if p 141 then d715 (change p 271 none) else d710 (change p 271 none)) = d186 p
  rw [sub2684, sub2679]
  simp only [ite_self]
theorem sub2686 (p : Pattern) : d717 (change p 271 none) = d187 p := by
  change (if p 134 then d702 (change p 271 none) else d716 (change p 271 none)) = d187 p
  rw [sub2671, sub2685]
  rfl
theorem sub2687 (p : Pattern) : d718 (change p 271 none) = d138 p := by
  change (if p 160 then d707 (change p 271 none) else d41 (change p 271 none)) = d138 p
  rw [sub2676, sub2622]
  rfl
theorem sub2688 (p : Pattern) : d719 (change p 271 none) = d140 p := by
  change (if p 159 then d708 (change p 271 none) else d718 (change p 271 none)) = d140 p
  rw [sub2677, sub2687]
  rfl
theorem sub2689 (p : Pattern) : d720 (change p 271 none) = d188 p := by
  change (if p 158 then d674 (change p 271 none) else d719 (change p 271 none)) = d188 p
  rw [sub2643, sub2688]
  rfl
theorem sub2690 (p : Pattern) : d721 (change p 271 none) = d138 p := by
  change (if p 160 then d712 (change p 271 none) else d43 (change p 271 none)) = d138 p
  rw [sub2681, sub2637]
  rfl
theorem sub2691 (p : Pattern) : d722 (change p 271 none) = d140 p := by
  change (if p 159 then d713 (change p 271 none) else d721 (change p 271 none)) = d140 p
  rw [sub2682, sub2690]
  rfl
theorem sub2692 (p : Pattern) : d723 (change p 271 none) = d188 p := by
  change (if p 158 then d684 (change p 271 none) else d722 (change p 271 none)) = d188 p
  rw [sub2653, sub2691]
  rfl
theorem sub2693 (p : Pattern) : d724 (change p 271 none) = d188 p := by
  change (if p 141 then d723 (change p 271 none) else d720 (change p 271 none)) = d188 p
  rw [sub2692, sub2689]
  simp only [ite_self]
theorem sub2694 (p : Pattern) : d725 (change p 271 none) = d189 p := by
  change (if p 134 then d702 (change p 271 none) else d724 (change p 271 none)) = d189 p
  rw [sub2671, sub2693]
  rfl
theorem sub2695 (p : Pattern) : d726 (change p 271 none) = d190 p := by
  change (if p 133 then d725 (change p 271 none) else d717 (change p 271 none)) = d190 p
  rw [sub2694, sub2686]
  rfl
theorem sub2696 (p : Pattern) : d727 (change p 271 none) = d191 p := by
  change (if p 158 then d674 (change p 271 none) else d709 (change p 271 none)) = d191 p
  rw [sub2643, sub2678]
  rfl
theorem sub2697 (p : Pattern) : d728 (change p 271 none) = d191 p := by
  change (if p 158 then d684 (change p 271 none) else d714 (change p 271 none)) = d191 p
  rw [sub2653, sub2683]
  rfl
theorem sub2698 (p : Pattern) : d729 (change p 271 none) = d191 p := by
  change (if p 141 then d728 (change p 271 none) else d727 (change p 271 none)) = d191 p
  rw [sub2697, sub2696]
  simp only [ite_self]
theorem sub2699 (p : Pattern) : d730 (change p 271 none) = d192 p := by
  change (if p 134 then d702 (change p 271 none) else d729 (change p 271 none)) = d192 p
  rw [sub2671, sub2698]
  rfl
theorem sub2700 (p : Pattern) : d731 (change p 271 none) = d193 p := by
  change (if p 133 then d702 (change p 271 none) else d730 (change p 271 none)) = d193 p
  rw [sub2671, sub2699]
  rfl
theorem sub2701 (p : Pattern) : d732 (change p 271 none) = d194 p := by
  change (if p 132 then d731 (change p 271 none) else d726 (change p 271 none)) = d194 p
  rw [sub2700, sub2695]
  rfl
theorem sub2702 (p : Pattern) : d733 (change p 271 none) = d195 p := by
  change (if p 108 then d732 (change p 271 none) else d704 (change p 271 none)) = d195 p
  rw [sub2701, sub2673]
  rfl
end NetHack.Sokoban12CostPartition
