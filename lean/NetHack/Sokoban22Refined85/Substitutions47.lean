/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions46
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5640 (p : Pattern) : d796 (change p 161 (some 160)) = d796 p := by
  change (if p 163 then d795 (change p 161 (some 160)) else d53 (change p 161 (some 160))) = d796 p
  rw [sub5639, sub5625]
  rfl
theorem sub5641 (p : Pattern) : d797 (change p 161 (some 160)) = d797 p := by
  change (if p 182 then d36 (change p 161 (some 160)) else d18 (change p 161 (some 160))) = d797 p
  rw [sub5629, sub5637]
  rfl
theorem sub5642 (p : Pattern) : d11 (change p 161 (some 160)) = d11 p := by
  rfl
theorem sub5643 (p : Pattern) : d39 (change p 161 (some 160)) = d39 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d11 (change p 161 (some 160))) = d39 p
  rw [sub5617, sub5642]
  rfl
theorem sub5644 (p : Pattern) : d40 (change p 161 (some 160)) = d40 p := by
  change (if p 246 then d39 (change p 161 (some 160)) else d11 (change p 161 (some 160))) = d40 p
  rw [sub5643, sub5642]
  rfl
theorem sub5645 (p : Pattern) : d41 (change p 161 (some 160)) = d41 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d40 (change p 161 (some 160))) = d41 p
  rw [sub5617, sub5644]
  rfl
theorem sub5646 (p : Pattern) : d62 (change p 161 (some 160)) = d62 p := by
  change (if p 182 then d41 (change p 161 (some 160)) else d40 (change p 161 (some 160))) = d62 p
  rw [sub5645, sub5644]
  rfl
theorem sub5647 (p : Pattern) : d798 (change p 161 (some 160)) = d798 p := by
  change (if p 163 then d62 (change p 161 (some 160)) else d797 (change p 161 (some 160))) = d798 p
  rw [sub5646, sub5641]
  rfl
theorem sub5648 (p : Pattern) : d799 (change p 161 (some 160)) = d799 p := by
  change (if p 162 then d798 (change p 161 (some 160)) else d796 (change p 161 (some 160))) = d799 p
  rw [sub5647, sub5640]
  rfl
theorem sub5649 (p : Pattern) : d800 (change p 161 (some 160)) = d799 p := by
  change d799 (change p 161 (some 160)) = d799 p
  exact sub5648 p
theorem sub5650 (p : Pattern) : d801 (change p 161 (some 160)) = d799 p := by
  change d800 (change p 161 (some 160)) = d799 p
  exact sub5649 p
theorem sub5651 (p : Pattern) : d802 (change p 161 (some 160)) = d4766 p := by
  change (if p 141 then d801 (change p 161 (some 160)) else d793 (change p 161 (some 160))) = d4766 p
  rw [sub5650, sub5634]
  rfl
theorem sub5652 (p : Pattern) : d804 (change p 161 (some 160)) = d804 p := by
  change (if p 162 then d79 (change p 161 (some 160)) else d53 (change p 161 (some 160))) = d804 p
  rw [sub5631, sub5625]
  rfl
theorem sub5653 (p : Pattern) : d805 (change p 161 (some 160)) = d804 p := by
  change d804 (change p 161 (some 160)) = d804 p
  exact sub5652 p
theorem sub5654 (p : Pattern) : d806 (change p 161 (some 160)) = d804 p := by
  change d805 (change p 161 (some 160)) = d804 p
  exact sub5653 p
theorem sub5655 (p : Pattern) : d20 (change p 161 (some 160)) = d20 p := by
  change (if p 182 then d19 (change p 161 (some 160)) else d18 (change p 161 (some 160))) = d20 p
  rw [sub5638, sub5637]
  rfl
theorem sub5656 (p : Pattern) : d808 (change p 161 (some 160)) = d808 p := by
  change (if p 163 then d20 (change p 161 (some 160)) else d53 (change p 161 (some 160))) = d808 p
  rw [sub5655, sub5625]
  rfl
theorem sub5657 (p : Pattern) : d809 (change p 161 (some 160)) = d809 p := by
  change (if p 163 then d62 (change p 161 (some 160)) else d78 (change p 161 (some 160))) = d809 p
  rw [sub5646, sub5630]
  rfl
theorem sub5658 (p : Pattern) : d810 (change p 161 (some 160)) = d810 p := by
  change (if p 162 then d809 (change p 161 (some 160)) else d808 (change p 161 (some 160))) = d810 p
  rw [sub5657, sub5656]
  rfl
theorem sub5659 (p : Pattern) : d811 (change p 161 (some 160)) = d810 p := by
  change d810 (change p 161 (some 160)) = d810 p
  exact sub5658 p
theorem sub5660 (p : Pattern) : d812 (change p 161 (some 160)) = d810 p := by
  change d811 (change p 161 (some 160)) = d810 p
  exact sub5659 p
theorem sub5661 (p : Pattern) : d813 (change p 161 (some 160)) = d4767 p := by
  change (if p 141 then d812 (change p 161 (some 160)) else d806 (change p 161 (some 160))) = d4767 p
  rw [sub5660, sub5654]
  rfl
theorem sub5662 (p : Pattern) : d814 (change p 161 (some 160)) = d4768 p := by
  change (if p 138 then d813 (change p 161 (some 160)) else d802 (change p 161 (some 160))) = d4768 p
  rw [sub5661, sub5651]
  rfl
theorem sub5663 (p : Pattern) : d816 (change p 161 (some 160)) = d804 p := by
  change d805 (change p 161 (some 160)) = d804 p
  exact sub5653 p
theorem sub5664 (p : Pattern) : d818 (change p 161 (some 160)) = d810 p := by
  change d811 (change p 161 (some 160)) = d810 p
  exact sub5659 p
theorem sub5665 (p : Pattern) : d819 (change p 161 (some 160)) = d4767 p := by
  change (if p 141 then d818 (change p 161 (some 160)) else d816 (change p 161 (some 160))) = d4767 p
  rw [sub5664, sub5663]
  rfl
theorem sub5666 (p : Pattern) : d63 (change p 161 (some 160)) = d63 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d62 (change p 161 (some 160))) = d63 p
  rw [sub5617, sub5646]
  rfl
theorem sub5667 (p : Pattern) : d91 (change p 161 (some 160)) = d91 p := by
  change (if p 162 then d12 (change p 161 (some 160)) else d63 (change p 161 (some 160))) = d91 p
  rw [sub5617, sub5666]
  rfl
theorem sub5668 (p : Pattern) : d93 (change p 161 (some 160)) = d91 p := by
  change d91 (change p 161 (some 160)) = d91 p
  exact sub5667 p
theorem sub5669 (p : Pattern) : d821 (change p 161 (some 160)) = d91 p := by
  change d93 (change p 161 (some 160)) = d91 p
  exact sub5668 p
theorem sub5670 (p : Pattern) : d95 (change p 161 (some 160)) = d12 p := by
  change d12 (change p 161 (some 160)) = d12 p
  exact sub5617 p
theorem sub5671 (p : Pattern) : d822 (change p 161 (some 160)) = d4434 p := by
  change (if p 141 then d95 (change p 161 (some 160)) else d821 (change p 161 (some 160))) = d4434 p
  rw [sub5670, sub5669]
  rfl
theorem sub5672 (p : Pattern) : d823 (change p 161 (some 160)) = d4769 p := by
  change (if p 138 then d822 (change p 161 (some 160)) else d819 (change p 161 (some 160))) = d4769 p
  rw [sub5671, sub5665]
  rfl
theorem sub5673 (p : Pattern) : d824 (change p 161 (some 160)) = d4770 p := by
  change (if p 116 then d823 (change p 161 (some 160)) else d814 (change p 161 (some 160))) = d4770 p
  rw [sub5672, sub5662]
  rfl
theorem sub5674 (p : Pattern) : d826 (change p 161 (some 160)) = d791 p := by
  change d791 (change p 161 (some 160)) = d791 p
  exact sub5632 p
theorem sub5675 (p : Pattern) : d827 (change p 161 (some 160)) = d791 p := by
  change d826 (change p 161 (some 160)) = d791 p
  exact sub5674 p
theorem sub5676 (p : Pattern) : d829 (change p 161 (some 160)) = d799 p := by
  change d800 (change p 161 (some 160)) = d799 p
  exact sub5649 p
theorem sub5677 (p : Pattern) : d830 (change p 161 (some 160)) = d4766 p := by
  change (if p 141 then d829 (change p 161 (some 160)) else d827 (change p 161 (some 160))) = d4766 p
  rw [sub5676, sub5675]
  rfl
theorem sub5678 (p : Pattern) : d832 (change p 161 (some 160)) = d804 p := by
  change d805 (change p 161 (some 160)) = d804 p
  exact sub5653 p
theorem sub5679 (p : Pattern) : d833 (change p 161 (some 160)) = d4767 p := by
  change (if p 141 then d812 (change p 161 (some 160)) else d832 (change p 161 (some 160))) = d4767 p
  rw [sub5660, sub5678]
  rfl
theorem sub5680 (p : Pattern) : d834 (change p 161 (some 160)) = d4768 p := by
  change (if p 138 then d833 (change p 161 (some 160)) else d830 (change p 161 (some 160))) = d4768 p
  rw [sub5679, sub5677]
  rfl
theorem sub5681 (p : Pattern) : d835 (change p 161 (some 160)) = d4771 p := by
  change (if p 138 then d12 (change p 161 (some 160)) else d833 (change p 161 (some 160))) = d4771 p
  rw [sub5617, sub5679]
  rfl
theorem sub5682 (p : Pattern) : d836 (change p 161 (some 160)) = d4772 p := by
  change (if p 116 then d835 (change p 161 (some 160)) else d834 (change p 161 (some 160))) = d4772 p
  rw [sub5681, sub5680]
  rfl
theorem sub5683 (p : Pattern) : d837 (change p 161 (some 160)) = d4773 p := by
  change (if p 115 then d836 (change p 161 (some 160)) else d824 (change p 161 (some 160))) = d4773 p
  rw [sub5682, sub5673]
  rfl
theorem sub5684 (p : Pattern) : d839 (change p 161 (some 160)) = d791 p := by
  change d826 (change p 161 (some 160)) = d791 p
  exact sub5674 p
theorem sub5685 (p : Pattern) : d841 (change p 161 (some 160)) = d799 p := by
  change d800 (change p 161 (some 160)) = d799 p
  exact sub5649 p
theorem sub5686 (p : Pattern) : d842 (change p 161 (some 160)) = d4766 p := by
  change (if p 141 then d841 (change p 161 (some 160)) else d839 (change p 161 (some 160))) = d4766 p
  rw [sub5685, sub5684]
  rfl
theorem sub5687 (p : Pattern) : d844 (change p 161 (some 160)) = d804 p := by
  change d805 (change p 161 (some 160)) = d804 p
  exact sub5653 p
theorem sub5688 (p : Pattern) : d845 (change p 161 (some 160)) = d4767 p := by
  change (if p 141 then d812 (change p 161 (some 160)) else d844 (change p 161 (some 160))) = d4767 p
  rw [sub5660, sub5687]
  rfl
theorem sub5689 (p : Pattern) : d846 (change p 161 (some 160)) = d4768 p := by
  change (if p 138 then d845 (change p 161 (some 160)) else d842 (change p 161 (some 160))) = d4768 p
  rw [sub5688, sub5686]
  rfl
theorem sub5690 (p : Pattern) : d847 (change p 161 (some 160)) = d4769 p := by
  change (if p 138 then d822 (change p 161 (some 160)) else d813 (change p 161 (some 160))) = d4769 p
  rw [sub5671, sub5661]
  rfl
theorem sub5691 (p : Pattern) : d848 (change p 161 (some 160)) = d4770 p := by
  change (if p 116 then d847 (change p 161 (some 160)) else d846 (change p 161 (some 160))) = d4770 p
  rw [sub5690, sub5689]
  rfl
theorem sub5692 (p : Pattern) : d849 (change p 161 (some 160)) = d791 p := by
  change d826 (change p 161 (some 160)) = d791 p
  exact sub5674 p
theorem sub5693 (p : Pattern) : d850 (change p 161 (some 160)) = d799 p := by
  change d800 (change p 161 (some 160)) = d799 p
  exact sub5649 p
theorem sub5694 (p : Pattern) : d851 (change p 161 (some 160)) = d4766 p := by
  change (if p 141 then d850 (change p 161 (some 160)) else d849 (change p 161 (some 160))) = d4766 p
  rw [sub5693, sub5692]
  rfl
theorem sub5695 (p : Pattern) : d852 (change p 161 (some 160)) = d4768 p := by
  change (if p 138 then d833 (change p 161 (some 160)) else d851 (change p 161 (some 160))) = d4768 p
  rw [sub5679, sub5694]
  rfl
theorem sub5696 (p : Pattern) : d853 (change p 161 (some 160)) = d4772 p := by
  change (if p 116 then d835 (change p 161 (some 160)) else d852 (change p 161 (some 160))) = d4772 p
  rw [sub5681, sub5695]
  rfl
theorem sub5697 (p : Pattern) : d854 (change p 161 (some 160)) = d4773 p := by
  change (if p 115 then d853 (change p 161 (some 160)) else d848 (change p 161 (some 160))) = d4773 p
  rw [sub5696, sub5691]
  rfl
theorem sub5698 (p : Pattern) : d855 (change p 161 (some 160)) = d4773 p := by
  change (if p 71 then d854 (change p 161 (some 160)) else d837 (change p 161 (some 160))) = d4773 p
  rw [sub5697, sub5683]
  simp only [ite_self]
theorem sub5699 (p : Pattern) : d1 (change p 161 (some 160)) = d1 p := by
  rfl
theorem sub5700 (p : Pattern) : d102 (change p 161 (some 160)) = d102 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d1 (change p 161 (some 160))) = d102 p
  rw [sub5617, sub5699]
  rfl
theorem sub5701 (p : Pattern) : d103 (change p 161 (some 160)) = d103 p := by
  change (if p 246 then d102 (change p 161 (some 160)) else d1 (change p 161 (some 160))) = d103 p
  rw [sub5700, sub5699]
  rfl
theorem sub5702 (p : Pattern) : d3 (change p 161 (some 160)) = d3 p := by
  rfl
theorem sub5703 (p : Pattern) : d115 (change p 161 (some 160)) = d115 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d3 (change p 161 (some 160))) = d115 p
  rw [sub5617, sub5702]
  rfl
theorem sub5704 (p : Pattern) : d116 (change p 161 (some 160)) = d116 p := by
  change (if p 246 then d115 (change p 161 (some 160)) else d3 (change p 161 (some 160))) = d116 p
  rw [sub5703, sub5702]
  rfl
theorem sub5705 (p : Pattern) : d117 (change p 161 (some 160)) = d117 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d116 (change p 161 (some 160))) = d117 p
  rw [sub5617, sub5704]
  rfl
theorem sub5706 (p : Pattern) : d118 (change p 161 (some 160)) = d118 p := by
  change (if p 182 then d117 (change p 161 (some 160)) else d103 (change p 161 (some 160))) = d118 p
  rw [sub5705, sub5701]
  rfl
theorem sub5707 (p : Pattern) : d132 (change p 161 (some 160)) = d132 p := by
  change (if p 182 then d117 (change p 161 (some 160)) else d116 (change p 161 (some 160))) = d132 p
  rw [sub5705, sub5704]
  rfl
theorem sub5708 (p : Pattern) : d7 (change p 161 (some 160)) = d7 p := by
  rfl
theorem sub5709 (p : Pattern) : d119 (change p 161 (some 160)) = d119 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d7 (change p 161 (some 160))) = d119 p
  rw [sub5617, sub5708]
  rfl
theorem sub5710 (p : Pattern) : d120 (change p 161 (some 160)) = d120 p := by
  change (if p 246 then d119 (change p 161 (some 160)) else d7 (change p 161 (some 160))) = d120 p
  rw [sub5709, sub5708]
  rfl
theorem sub5711 (p : Pattern) : d121 (change p 161 (some 160)) = d121 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d120 (change p 161 (some 160))) = d121 p
  rw [sub5617, sub5710]
  rfl
theorem sub5712 (p : Pattern) : d148 (change p 161 (some 160)) = d148 p := by
  change (if p 182 then d121 (change p 161 (some 160)) else d120 (change p 161 (some 160))) = d148 p
  rw [sub5711, sub5710]
  rfl
theorem sub5713 (p : Pattern) : d149 (change p 161 (some 160)) = d149 p := by
  change (if p 163 then d148 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d149 p
  rw [sub5712, sub5707]
  rfl
theorem sub5714 (p : Pattern) : d857 (change p 161 (some 160)) = d857 p := by
  change (if p 162 then d149 (change p 161 (some 160)) else d118 (change p 161 (some 160))) = d857 p
  rw [sub5713, sub5706]
  rfl
theorem sub5715 (p : Pattern) : d858 (change p 161 (some 160)) = d857 p := by
  change d857 (change p 161 (some 160)) = d857 p
  exact sub5714 p
theorem sub5716 (p : Pattern) : d859 (change p 161 (some 160)) = d857 p := by
  change d858 (change p 161 (some 160)) = d857 p
  exact sub5715 p
theorem sub5717 (p : Pattern) : d5 (change p 161 (some 160)) = d5 p := by
  rfl
theorem sub5718 (p : Pattern) : d106 (change p 161 (some 160)) = d106 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d5 (change p 161 (some 160))) = d106 p
  rw [sub5617, sub5717]
  rfl
theorem sub5719 (p : Pattern) : d107 (change p 161 (some 160)) = d107 p := by
  change (if p 246 then d106 (change p 161 (some 160)) else d5 (change p 161 (some 160))) = d107 p
  rw [sub5718, sub5717]
  rfl
theorem sub5720 (p : Pattern) : d108 (change p 161 (some 160)) = d108 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d107 (change p 161 (some 160))) = d108 p
  rw [sub5617, sub5719]
  rfl
theorem sub5721 (p : Pattern) : d861 (change p 161 (some 160)) = d861 p := by
  change (if p 182 then d108 (change p 161 (some 160)) else d116 (change p 161 (some 160))) = d861 p
  rw [sub5720, sub5704]
  rfl
theorem sub5722 (p : Pattern) : d862 (change p 161 (some 160)) = d862 p := by
  change (if p 163 then d861 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d862 p
  rw [sub5721, sub5707]
  rfl
theorem sub5723 (p : Pattern) : d234 (change p 161 (some 160)) = d234 p := by
  change (if p 182 then d121 (change p 161 (some 160)) else d107 (change p 161 (some 160))) = d234 p
  rw [sub5711, sub5719]
  rfl
theorem sub5724 (p : Pattern) : d863 (change p 161 (some 160)) = d863 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d234 (change p 161 (some 160))) = d863 p
  rw [sub5617, sub5723]
  rfl
theorem sub5725 (p : Pattern) : d864 (change p 161 (some 160)) = d864 p := by
  change (if p 162 then d863 (change p 161 (some 160)) else d862 (change p 161 (some 160))) = d864 p
  rw [sub5724, sub5722]
  rfl
theorem sub5726 (p : Pattern) : d865 (change p 161 (some 160)) = d864 p := by
  change d864 (change p 161 (some 160)) = d864 p
  exact sub5725 p
theorem sub5727 (p : Pattern) : d866 (change p 161 (some 160)) = d864 p := by
  change d865 (change p 161 (some 160)) = d864 p
  exact sub5726 p
theorem sub5728 (p : Pattern) : d867 (change p 161 (some 160)) = d4774 p := by
  change (if p 141 then d866 (change p 161 (some 160)) else d859 (change p 161 (some 160))) = d4774 p
  rw [sub5727, sub5716]
  rfl
theorem sub5729 (p : Pattern) : d869 (change p 161 (some 160)) = d869 p := by
  change (if p 162 then d149 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d869 p
  rw [sub5713, sub5707]
  rfl
theorem sub5730 (p : Pattern) : d870 (change p 161 (some 160)) = d869 p := by
  change d869 (change p 161 (some 160)) = d869 p
  exact sub5729 p
theorem sub5731 (p : Pattern) : d871 (change p 161 (some 160)) = d869 p := by
  change d870 (change p 161 (some 160)) = d869 p
  exact sub5730 p
theorem sub5732 (p : Pattern) : d109 (change p 161 (some 160)) = d109 p := by
  change (if p 182 then d108 (change p 161 (some 160)) else d107 (change p 161 (some 160))) = d109 p
  rw [sub5720, sub5719]
  rfl
theorem sub5733 (p : Pattern) : d873 (change p 161 (some 160)) = d873 p := by
  change (if p 163 then d109 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d873 p
  rw [sub5732, sub5707]
  rfl
theorem sub5734 (p : Pattern) : d153 (change p 161 (some 160)) = d153 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d148 (change p 161 (some 160))) = d153 p
  rw [sub5617, sub5712]
  rfl
theorem sub5735 (p : Pattern) : d874 (change p 161 (some 160)) = d874 p := by
  change (if p 162 then d153 (change p 161 (some 160)) else d873 (change p 161 (some 160))) = d874 p
  rw [sub5734, sub5733]
  rfl
theorem sub5736 (p : Pattern) : d875 (change p 161 (some 160)) = d874 p := by
  change d874 (change p 161 (some 160)) = d874 p
  exact sub5735 p
theorem sub5737 (p : Pattern) : d876 (change p 161 (some 160)) = d874 p := by
  change d875 (change p 161 (some 160)) = d874 p
  exact sub5736 p
theorem sub5738 (p : Pattern) : d877 (change p 161 (some 160)) = d4775 p := by
  change (if p 141 then d876 (change p 161 (some 160)) else d871 (change p 161 (some 160))) = d4775 p
  rw [sub5737, sub5731]
  rfl
theorem sub5739 (p : Pattern) : d878 (change p 161 (some 160)) = d4776 p := by
  change (if p 138 then d877 (change p 161 (some 160)) else d867 (change p 161 (some 160))) = d4776 p
  rw [sub5738, sub5728]
  rfl
theorem sub5740 (p : Pattern) : d880 (change p 161 (some 160)) = d869 p := by
  change d870 (change p 161 (some 160)) = d869 p
  exact sub5730 p
theorem sub5741 (p : Pattern) : d881 (change p 161 (some 160)) = d4775 p := by
  change (if p 141 then d876 (change p 161 (some 160)) else d880 (change p 161 (some 160))) = d4775 p
  rw [sub5737, sub5740]
  rfl
theorem sub5742 (p : Pattern) : d161 (change p 161 (some 160)) = d12 p := by
  change d12 (change p 161 (some 160)) = d12 p
  exact sub5617 p
theorem sub5743 (p : Pattern) : d162 (change p 161 (some 160)) = d12 p := by
  change (if p 141 then d12 (change p 161 (some 160)) else d161 (change p 161 (some 160))) = d12 p
  rw [sub5617, sub5742]
  simp only [ite_self]
theorem sub5744 (p : Pattern) : d882 (change p 161 (some 160)) = d4777 p := by
  change (if p 138 then d162 (change p 161 (some 160)) else d881 (change p 161 (some 160))) = d4777 p
  rw [sub5743, sub5741]
  rfl
theorem sub5745 (p : Pattern) : d883 (change p 161 (some 160)) = d4778 p := by
  change (if p 116 then d882 (change p 161 (some 160)) else d878 (change p 161 (some 160))) = d4778 p
  rw [sub5744, sub5739]
  rfl
theorem sub5746 (p : Pattern) : d885 (change p 161 (some 160)) = d857 p := by
  change d858 (change p 161 (some 160)) = d857 p
  exact sub5715 p
theorem sub5747 (p : Pattern) : d887 (change p 161 (some 160)) = d864 p := by
  change d865 (change p 161 (some 160)) = d864 p
  exact sub5726 p
theorem sub5748 (p : Pattern) : d888 (change p 161 (some 160)) = d4774 p := by
  change (if p 141 then d887 (change p 161 (some 160)) else d885 (change p 161 (some 160))) = d4774 p
  rw [sub5747, sub5746]
  rfl
theorem sub5749 (p : Pattern) : d890 (change p 161 (some 160)) = d869 p := by
  change d870 (change p 161 (some 160)) = d869 p
  exact sub5730 p
theorem sub5750 (p : Pattern) : d891 (change p 161 (some 160)) = d4775 p := by
  change (if p 141 then d876 (change p 161 (some 160)) else d890 (change p 161 (some 160))) = d4775 p
  rw [sub5737, sub5749]
  rfl
theorem sub5751 (p : Pattern) : d892 (change p 161 (some 160)) = d4776 p := by
  change (if p 138 then d891 (change p 161 (some 160)) else d888 (change p 161 (some 160))) = d4776 p
  rw [sub5750, sub5748]
  rfl
theorem sub5752 (p : Pattern) : d893 (change p 161 (some 160)) = d4777 p := by
  change (if p 138 then d12 (change p 161 (some 160)) else d891 (change p 161 (some 160))) = d4777 p
  rw [sub5617, sub5750]
  rfl
theorem sub5753 (p : Pattern) : d894 (change p 161 (some 160)) = d4778 p := by
  change (if p 116 then d893 (change p 161 (some 160)) else d892 (change p 161 (some 160))) = d4778 p
  rw [sub5752, sub5751]
  rfl
theorem sub5754 (p : Pattern) : d895 (change p 161 (some 160)) = d4778 p := by
  change (if p 115 then d894 (change p 161 (some 160)) else d883 (change p 161 (some 160))) = d4778 p
  rw [sub5753, sub5745]
  simp only [ite_self]
theorem sub5755 (p : Pattern) : d896 (change p 161 (some 160)) = d4779 p := by
  change (if p 71 then d895 (change p 161 (some 160)) else d837 (change p 161 (some 160))) = d4779 p
  rw [sub5754, sub5683]
  rfl
theorem sub5756 (p : Pattern) : d897 (change p 161 (some 160)) = d4780 p := by
  change (if p 49 then d896 (change p 161 (some 160)) else d855 (change p 161 (some 160))) = d4780 p
  rw [sub5755, sub5698]
  rfl
theorem sub5757 (p : Pattern) : d8 (change p 161 (some 160)) = d8 p := by
  rfl
theorem sub5758 (p : Pattern) : d190 (change p 161 (some 160)) = d190 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d8 (change p 161 (some 160))) = d190 p
  rw [sub5617, sub5757]
  rfl
theorem sub5759 (p : Pattern) : d191 (change p 161 (some 160)) = d191 p := by
  change (if p 246 then d190 (change p 161 (some 160)) else d8 (change p 161 (some 160))) = d191 p
  rw [sub5758, sub5757]
  rfl
end NetHack.Sokoban22Refined85
