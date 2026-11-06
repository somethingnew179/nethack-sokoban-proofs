/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions47
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5760 (p : Pattern) : d192 (change p 161 (some 160)) = d192 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d191 (change p 161 (some 160))) = d192 p
  rw [sub5617, sub5759]
  rfl
theorem sub5761 (p : Pattern) : d193 (change p 161 (some 160)) = d193 p := by
  change (if p 182 then d192 (change p 161 (some 160)) else d191 (change p 161 (some 160))) = d193 p
  rw [sub5760, sub5759]
  rfl
theorem sub5762 (p : Pattern) : d194 (change p 161 (some 160)) = d194 p := by
  change (if p 163 then d193 (change p 161 (some 160)) else d20 (change p 161 (some 160))) = d194 p
  rw [sub5761, sub5655]
  rfl
theorem sub5763 (p : Pattern) : d899 (change p 161 (some 160)) = d899 p := by
  change (if p 162 then d194 (change p 161 (some 160)) else d53 (change p 161 (some 160))) = d899 p
  rw [sub5762, sub5625]
  rfl
theorem sub5764 (p : Pattern) : d900 (change p 161 (some 160)) = d899 p := by
  change d899 (change p 161 (some 160)) = d899 p
  exact sub5763 p
theorem sub5765 (p : Pattern) : d901 (change p 161 (some 160)) = d899 p := by
  change d900 (change p 161 (some 160)) = d899 p
  exact sub5764 p
theorem sub5766 (p : Pattern) : d83 (change p 161 (some 160)) = d83 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d78 (change p 161 (some 160))) = d83 p
  rw [sub5617, sub5630]
  rfl
theorem sub5767 (p : Pattern) : d903 (change p 161 (some 160)) = d903 p := by
  change (if p 162 then d83 (change p 161 (some 160)) else d20 (change p 161 (some 160))) = d903 p
  rw [sub5766, sub5655]
  rfl
theorem sub5768 (p : Pattern) : d904 (change p 161 (some 160)) = d903 p := by
  change d903 (change p 161 (some 160)) = d903 p
  exact sub5767 p
theorem sub5769 (p : Pattern) : d905 (change p 161 (some 160)) = d903 p := by
  change d904 (change p 161 (some 160)) = d903 p
  exact sub5768 p
theorem sub5770 (p : Pattern) : d906 (change p 161 (some 160)) = d4781 p := by
  change (if p 141 then d905 (change p 161 (some 160)) else d901 (change p 161 (some 160))) = d4781 p
  rw [sub5769, sub5765]
  rfl
theorem sub5771 (p : Pattern) : d907 (change p 161 (some 160)) = d4782 p := by
  change (if p 138 then d906 (change p 161 (some 160)) else d851 (change p 161 (some 160))) = d4782 p
  rw [sub5770, sub5694]
  rfl
theorem sub5772 (p : Pattern) : d908 (change p 161 (some 160)) = d4783 p := by
  change (if p 138 then d12 (change p 161 (some 160)) else d906 (change p 161 (some 160))) = d4783 p
  rw [sub5617, sub5770]
  rfl
theorem sub5773 (p : Pattern) : d909 (change p 161 (some 160)) = d4784 p := by
  change (if p 116 then d908 (change p 161 (some 160)) else d907 (change p 161 (some 160))) = d4784 p
  rw [sub5772, sub5771]
  rfl
theorem sub5774 (p : Pattern) : d910 (change p 161 (some 160)) = d4785 p := by
  change (if p 115 then d909 (change p 161 (some 160)) else d848 (change p 161 (some 160))) = d4785 p
  rw [sub5773, sub5691]
  rfl
theorem sub5775 (p : Pattern) : d911 (change p 161 (some 160)) = d4786 p := by
  change (if p 71 then d910 (change p 161 (some 160)) else d837 (change p 161 (some 160))) = d4786 p
  rw [sub5774, sub5683]
  rfl
theorem sub5776 (p : Pattern) : d913 (change p 161 (some 160)) = d864 p := by
  change d865 (change p 161 (some 160)) = d864 p
  exact sub5726 p
theorem sub5777 (p : Pattern) : d914 (change p 161 (some 160)) = d4774 p := by
  change (if p 141 then d913 (change p 161 (some 160)) else d859 (change p 161 (some 160))) = d4774 p
  rw [sub5776, sub5716]
  rfl
theorem sub5778 (p : Pattern) : d916 (change p 161 (some 160)) = d874 p := by
  change d875 (change p 161 (some 160)) = d874 p
  exact sub5736 p
theorem sub5779 (p : Pattern) : d917 (change p 161 (some 160)) = d4775 p := by
  change (if p 141 then d916 (change p 161 (some 160)) else d871 (change p 161 (some 160))) = d4775 p
  rw [sub5778, sub5731]
  rfl
theorem sub5780 (p : Pattern) : d918 (change p 161 (some 160)) = d4776 p := by
  change (if p 138 then d917 (change p 161 (some 160)) else d914 (change p 161 (some 160))) = d4776 p
  rw [sub5779, sub5777]
  rfl
theorem sub5781 (p : Pattern) : d919 (change p 161 (some 160)) = d4775 p := by
  change (if p 141 then d916 (change p 161 (some 160)) else d880 (change p 161 (some 160))) = d4775 p
  rw [sub5778, sub5740]
  rfl
theorem sub5782 (p : Pattern) : d920 (change p 161 (some 160)) = d4777 p := by
  change (if p 138 then d162 (change p 161 (some 160)) else d919 (change p 161 (some 160))) = d4777 p
  rw [sub5743, sub5781]
  rfl
theorem sub5783 (p : Pattern) : d921 (change p 161 (some 160)) = d4778 p := by
  change (if p 116 then d920 (change p 161 (some 160)) else d918 (change p 161 (some 160))) = d4778 p
  rw [sub5782, sub5780]
  rfl
theorem sub5784 (p : Pattern) : d268 (change p 161 (some 160)) = d268 p := by
  change (if p 204 then d116 (change p 161 (some 160)) else d103 (change p 161 (some 160))) = d268 p
  rw [sub5704, sub5701]
  rfl
theorem sub5785 (p : Pattern) : d269 (change p 161 (some 160)) = d269 p := by
  change (if p 182 then d117 (change p 161 (some 160)) else d268 (change p 161 (some 160))) = d269 p
  rw [sub5705, sub5784]
  rfl
theorem sub5786 (p : Pattern) : d922 (change p 161 (some 160)) = d922 p := by
  change (if p 162 then d149 (change p 161 (some 160)) else d269 (change p 161 (some 160))) = d922 p
  rw [sub5713, sub5785]
  rfl
theorem sub5787 (p : Pattern) : d923 (change p 161 (some 160)) = d922 p := by
  change d922 (change p 161 (some 160)) = d922 p
  exact sub5786 p
theorem sub5788 (p : Pattern) : d924 (change p 161 (some 160)) = d922 p := by
  change d923 (change p 161 (some 160)) = d922 p
  exact sub5787 p
theorem sub5789 (p : Pattern) : d282 (change p 161 (some 160)) = d282 p := by
  change (if p 204 then d107 (change p 161 (some 160)) else d116 (change p 161 (some 160))) = d282 p
  rw [sub5719, sub5704]
  rfl
theorem sub5790 (p : Pattern) : d298 (change p 161 (some 160)) = d298 p := by
  change (if p 182 then d108 (change p 161 (some 160)) else d282 (change p 161 (some 160))) = d298 p
  rw [sub5720, sub5789]
  rfl
theorem sub5791 (p : Pattern) : d925 (change p 161 (some 160)) = d925 p := by
  change (if p 163 then d298 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d925 p
  rw [sub5790, sub5707]
  rfl
theorem sub5792 (p : Pattern) : d273 (change p 161 (some 160)) = d273 p := by
  change (if p 204 then d120 (change p 161 (some 160)) else d107 (change p 161 (some 160))) = d273 p
  rw [sub5710, sub5719]
  rfl
theorem sub5793 (p : Pattern) : d292 (change p 161 (some 160)) = d292 p := by
  change (if p 182 then d121 (change p 161 (some 160)) else d273 (change p 161 (some 160))) = d292 p
  rw [sub5711, sub5792]
  rfl
theorem sub5794 (p : Pattern) : d300 (change p 161 (some 160)) = d300 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d292 (change p 161 (some 160))) = d300 p
  rw [sub5617, sub5793]
  rfl
theorem sub5795 (p : Pattern) : d926 (change p 161 (some 160)) = d926 p := by
  change (if p 162 then d300 (change p 161 (some 160)) else d925 (change p 161 (some 160))) = d926 p
  rw [sub5794, sub5791]
  rfl
theorem sub5796 (p : Pattern) : d927 (change p 161 (some 160)) = d926 p := by
  change d926 (change p 161 (some 160)) = d926 p
  exact sub5795 p
theorem sub5797 (p : Pattern) : d928 (change p 161 (some 160)) = d926 p := by
  change d927 (change p 161 (some 160)) = d926 p
  exact sub5796 p
theorem sub5798 (p : Pattern) : d929 (change p 161 (some 160)) = d4787 p := by
  change (if p 141 then d928 (change p 161 (some 160)) else d924 (change p 161 (some 160))) = d4787 p
  rw [sub5797, sub5788]
  rfl
theorem sub5799 (p : Pattern) : d211 (change p 161 (some 160)) = d211 p := by
  change (if p 163 then d12 (change p 161 (some 160)) else d109 (change p 161 (some 160))) = d211 p
  rw [sub5617, sub5732]
  rfl
theorem sub5800 (p : Pattern) : d245 (change p 161 (some 160)) = d245 p := by
  change (if p 162 then d211 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d245 p
  rw [sub5799, sub5707]
  rfl
theorem sub5801 (p : Pattern) : d931 (change p 161 (some 160)) = d245 p := by
  change d245 (change p 161 (some 160)) = d245 p
  exact sub5800 p
theorem sub5802 (p : Pattern) : d932 (change p 161 (some 160)) = d245 p := by
  change d931 (change p 161 (some 160)) = d245 p
  exact sub5801 p
theorem sub5803 (p : Pattern) : d933 (change p 161 (some 160)) = d933 p := by
  change (if p 162 then d153 (change p 161 (some 160)) else d109 (change p 161 (some 160))) = d933 p
  rw [sub5734, sub5732]
  rfl
theorem sub5804 (p : Pattern) : d934 (change p 161 (some 160)) = d933 p := by
  change d933 (change p 161 (some 160)) = d933 p
  exact sub5803 p
theorem sub5805 (p : Pattern) : d935 (change p 161 (some 160)) = d933 p := by
  change d934 (change p 161 (some 160)) = d933 p
  exact sub5804 p
theorem sub5806 (p : Pattern) : d936 (change p 161 (some 160)) = d4788 p := by
  change (if p 141 then d935 (change p 161 (some 160)) else d932 (change p 161 (some 160))) = d4788 p
  rw [sub5805, sub5802]
  rfl
theorem sub5807 (p : Pattern) : d937 (change p 161 (some 160)) = d4789 p := by
  change (if p 138 then d936 (change p 161 (some 160)) else d929 (change p 161 (some 160))) = d4789 p
  rw [sub5806, sub5798]
  rfl
theorem sub5808 (p : Pattern) : d136 (change p 161 (some 160)) = d136 p := by
  change (if p 163 then d62 (change p 161 (some 160)) else d109 (change p 161 (some 160))) = d136 p
  rw [sub5646, sub5732]
  rfl
theorem sub5809 (p : Pattern) : d939 (change p 161 (some 160)) = d939 p := by
  change (if p 162 then d136 (change p 161 (some 160)) else d132 (change p 161 (some 160))) = d939 p
  rw [sub5808, sub5707]
  rfl
theorem sub5810 (p : Pattern) : d940 (change p 161 (some 160)) = d939 p := by
  change d939 (change p 161 (some 160)) = d939 p
  exact sub5809 p
theorem sub5811 (p : Pattern) : d941 (change p 161 (some 160)) = d939 p := by
  change d940 (change p 161 (some 160)) = d939 p
  exact sub5810 p
theorem sub5812 (p : Pattern) : d942 (change p 161 (some 160)) = d4790 p := by
  change (if p 141 then d935 (change p 161 (some 160)) else d941 (change p 161 (some 160))) = d4790 p
  rw [sub5805, sub5811]
  rfl
theorem sub5813 (p : Pattern) : d943 (change p 161 (some 160)) = d4791 p := by
  change (if p 138 then d12 (change p 161 (some 160)) else d942 (change p 161 (some 160))) = d4791 p
  rw [sub5617, sub5812]
  rfl
theorem sub5814 (p : Pattern) : d944 (change p 161 (some 160)) = d4792 p := by
  change (if p 116 then d943 (change p 161 (some 160)) else d937 (change p 161 (some 160))) = d4792 p
  rw [sub5813, sub5807]
  rfl
theorem sub5815 (p : Pattern) : d945 (change p 161 (some 160)) = d4793 p := by
  change (if p 115 then d944 (change p 161 (some 160)) else d921 (change p 161 (some 160))) = d4793 p
  rw [sub5814, sub5783]
  rfl
theorem sub5816 (p : Pattern) : d946 (change p 161 (some 160)) = d4794 p := by
  change (if p 71 then d945 (change p 161 (some 160)) else d837 (change p 161 (some 160))) = d4794 p
  rw [sub5815, sub5683]
  rfl
theorem sub5817 (p : Pattern) : d947 (change p 161 (some 160)) = d4795 p := by
  change (if p 49 then d946 (change p 161 (some 160)) else d911 (change p 161 (some 160))) = d4795 p
  rw [sub5816, sub5775]
  rfl
theorem sub5818 (p : Pattern) : d948 (change p 161 (some 160)) = d4796 p := by
  change (if p 48 then d947 (change p 161 (some 160)) else d897 (change p 161 (some 160))) = d4796 p
  rw [sub5817, sub5756]
  rfl
theorem sub5819 (p : Pattern) : d0 (change p 141 none) = d0 p := by
  rfl
theorem sub5820 (p : Pattern) : d12 (change p 141 none) = d12 p := by
  rfl
theorem sub5821 (p : Pattern) : d13 (change p 141 none) = d13 p := by
  change (if p 247 then d12 (change p 141 none) else d0 (change p 141 none)) = d13 p
  rw [sub5820, sub5819]
  rfl
theorem sub5822 (p : Pattern) : d14 (change p 141 none) = d14 p := by
  change (if p 246 then d13 (change p 141 none) else d0 (change p 141 none)) = d14 p
  rw [sub5821, sub5819]
  rfl
theorem sub5823 (p : Pattern) : d15 (change p 141 none) = d15 p := by
  change (if p 204 then d12 (change p 141 none) else d14 (change p 141 none)) = d15 p
  rw [sub5820, sub5822]
  rfl
theorem sub5824 (p : Pattern) : d16 (change p 141 none) = d16 p := by
  change (if p 182 then d15 (change p 141 none) else d14 (change p 141 none)) = d16 p
  rw [sub5823, sub5822]
  rfl
theorem sub5825 (p : Pattern) : d4 (change p 141 none) = d4 p := by
  rfl
theorem sub5826 (p : Pattern) : d17 (change p 141 none) = d17 p := by
  change (if p 247 then d12 (change p 141 none) else d4 (change p 141 none)) = d17 p
  rw [sub5820, sub5825]
  rfl
theorem sub5827 (p : Pattern) : d18 (change p 141 none) = d18 p := by
  change (if p 246 then d17 (change p 141 none) else d4 (change p 141 none)) = d18 p
  rw [sub5826, sub5825]
  rfl
theorem sub5828 (p : Pattern) : d19 (change p 141 none) = d19 p := by
  change (if p 204 then d12 (change p 141 none) else d18 (change p 141 none)) = d19 p
  rw [sub5820, sub5827]
  rfl
theorem sub5829 (p : Pattern) : d20 (change p 141 none) = d20 p := by
  change (if p 182 then d19 (change p 141 none) else d18 (change p 141 none)) = d20 p
  rw [sub5828, sub5827]
  rfl
theorem sub5830 (p : Pattern) : d21 (change p 141 none) = d21 p := by
  change (if p 163 then d20 (change p 141 none) else d16 (change p 141 none)) = d21 p
  rw [sub5829, sub5824]
  rfl
theorem sub5831 (p : Pattern) : d22 (change p 141 none) = d22 p := by
  change (if p 162 then d21 (change p 141 none) else d16 (change p 141 none)) = d22 p
  rw [sub5830, sub5824]
  rfl
theorem sub5832 (p : Pattern) : d9 (change p 141 none) = d9 p := by
  rfl
theorem sub5833 (p : Pattern) : d23 (change p 141 none) = d23 p := by
  change (if p 247 then d12 (change p 141 none) else d9 (change p 141 none)) = d23 p
  rw [sub5820, sub5832]
  rfl
theorem sub5834 (p : Pattern) : d24 (change p 141 none) = d24 p := by
  change (if p 246 then d23 (change p 141 none) else d9 (change p 141 none)) = d24 p
  rw [sub5833, sub5832]
  rfl
theorem sub5835 (p : Pattern) : d25 (change p 141 none) = d25 p := by
  change (if p 204 then d12 (change p 141 none) else d24 (change p 141 none)) = d25 p
  rw [sub5820, sub5834]
  rfl
theorem sub5836 (p : Pattern) : d26 (change p 141 none) = d26 p := by
  change (if p 182 then d25 (change p 141 none) else d24 (change p 141 none)) = d26 p
  rw [sub5835, sub5834]
  rfl
theorem sub5837 (p : Pattern) : d27 (change p 141 none) = d27 p := by
  change (if p 163 then d12 (change p 141 none) else d26 (change p 141 none)) = d27 p
  rw [sub5820, sub5836]
  rfl
theorem sub5838 (p : Pattern) : d28 (change p 141 none) = d28 p := by
  change (if p 162 then d27 (change p 141 none) else d21 (change p 141 none)) = d28 p
  rw [sub5837, sub5830]
  rfl
theorem sub5839 (p : Pattern) : d29 (change p 141 none) = d29 p := by
  change (if p 161 then d28 (change p 141 none) else d22 (change p 141 none)) = d29 p
  rw [sub5838, sub5831]
  rfl
theorem sub5840 (p : Pattern) : d2 (change p 141 none) = d2 p := by
  rfl
theorem sub5841 (p : Pattern) : d30 (change p 141 none) = d30 p := by
  change (if p 247 then d12 (change p 141 none) else d2 (change p 141 none)) = d30 p
  rw [sub5820, sub5840]
  rfl
theorem sub5842 (p : Pattern) : d31 (change p 141 none) = d31 p := by
  change (if p 246 then d30 (change p 141 none) else d2 (change p 141 none)) = d31 p
  rw [sub5841, sub5840]
  rfl
theorem sub5843 (p : Pattern) : d32 (change p 141 none) = d32 p := by
  change (if p 204 then d12 (change p 141 none) else d31 (change p 141 none)) = d32 p
  rw [sub5820, sub5842]
  rfl
theorem sub5844 (p : Pattern) : d33 (change p 141 none) = d33 p := by
  change (if p 182 then d32 (change p 141 none) else d14 (change p 141 none)) = d33 p
  rw [sub5843, sub5822]
  rfl
theorem sub5845 (p : Pattern) : d6 (change p 141 none) = d6 p := by
  rfl
theorem sub5846 (p : Pattern) : d34 (change p 141 none) = d34 p := by
  change (if p 247 then d12 (change p 141 none) else d6 (change p 141 none)) = d34 p
  rw [sub5820, sub5845]
  rfl
theorem sub5847 (p : Pattern) : d35 (change p 141 none) = d35 p := by
  change (if p 246 then d34 (change p 141 none) else d6 (change p 141 none)) = d35 p
  rw [sub5846, sub5845]
  rfl
theorem sub5848 (p : Pattern) : d36 (change p 141 none) = d36 p := by
  change (if p 204 then d12 (change p 141 none) else d35 (change p 141 none)) = d36 p
  rw [sub5820, sub5847]
  rfl
theorem sub5849 (p : Pattern) : d37 (change p 141 none) = d37 p := by
  change (if p 182 then d36 (change p 141 none) else d14 (change p 141 none)) = d37 p
  rw [sub5848, sub5822]
  rfl
theorem sub5850 (p : Pattern) : d38 (change p 141 none) = d38 p := by
  change (if p 163 then d37 (change p 141 none) else d33 (change p 141 none)) = d38 p
  rw [sub5849, sub5844]
  rfl
theorem sub5851 (p : Pattern) : d11 (change p 141 none) = d11 p := by
  rfl
theorem sub5852 (p : Pattern) : d39 (change p 141 none) = d39 p := by
  change (if p 247 then d12 (change p 141 none) else d11 (change p 141 none)) = d39 p
  rw [sub5820, sub5851]
  rfl
theorem sub5853 (p : Pattern) : d40 (change p 141 none) = d40 p := by
  change (if p 246 then d39 (change p 141 none) else d11 (change p 141 none)) = d40 p
  rw [sub5852, sub5851]
  rfl
theorem sub5854 (p : Pattern) : d41 (change p 141 none) = d41 p := by
  change (if p 204 then d12 (change p 141 none) else d40 (change p 141 none)) = d41 p
  rw [sub5820, sub5853]
  rfl
theorem sub5855 (p : Pattern) : d42 (change p 141 none) = d42 p := by
  change (if p 182 then d41 (change p 141 none) else d14 (change p 141 none)) = d42 p
  rw [sub5854, sub5822]
  rfl
theorem sub5856 (p : Pattern) : d43 (change p 141 none) = d43 p := by
  change (if p 182 then d12 (change p 141 none) else d18 (change p 141 none)) = d43 p
  rw [sub5820, sub5827]
  rfl
theorem sub5857 (p : Pattern) : d44 (change p 141 none) = d44 p := by
  change (if p 163 then d43 (change p 141 none) else d42 (change p 141 none)) = d44 p
  rw [sub5856, sub5855]
  rfl
theorem sub5858 (p : Pattern) : d45 (change p 141 none) = d45 p := by
  change (if p 162 then d44 (change p 141 none) else d38 (change p 141 none)) = d45 p
  rw [sub5857, sub5850]
  rfl
theorem sub5859 (p : Pattern) : d46 (change p 141 none) = d46 p := by
  change (if p 182 then d12 (change p 141 none) else d14 (change p 141 none)) = d46 p
  rw [sub5820, sub5822]
  rfl
theorem sub5860 (p : Pattern) : d47 (change p 141 none) = d47 p := by
  change (if p 163 then d43 (change p 141 none) else d46 (change p 141 none)) = d47 p
  rw [sub5856, sub5859]
  rfl
theorem sub5861 (p : Pattern) : d48 (change p 141 none) = d48 p := by
  change (if p 182 then d12 (change p 141 none) else d24 (change p 141 none)) = d48 p
  rw [sub5820, sub5834]
  rfl
theorem sub5862 (p : Pattern) : d49 (change p 141 none) = d49 p := by
  change (if p 163 then d12 (change p 141 none) else d48 (change p 141 none)) = d49 p
  rw [sub5820, sub5861]
  rfl
theorem sub5863 (p : Pattern) : d50 (change p 141 none) = d50 p := by
  change (if p 162 then d49 (change p 141 none) else d47 (change p 141 none)) = d50 p
  rw [sub5862, sub5860]
  rfl
theorem sub5864 (p : Pattern) : d51 (change p 141 none) = d51 p := by
  change (if p 161 then d50 (change p 141 none) else d45 (change p 141 none)) = d51 p
  rw [sub5863, sub5858]
  rfl
theorem sub5865 (p : Pattern) : d52 (change p 141 none) = d52 p := by
  change (if p 160 then d51 (change p 141 none) else d29 (change p 141 none)) = d52 p
  rw [sub5864, sub5839]
  rfl
theorem sub5866 (p : Pattern) : d653 (change p 141 none) = d52 p := by
  change d52 (change p 141 none) = d52 p
  exact sub5865 p
theorem sub5867 (p : Pattern) : d53 (change p 141 none) = d53 p := by
  change (if p 182 then d32 (change p 141 none) else d31 (change p 141 none)) = d53 p
  rw [sub5843, sub5842]
  rfl
theorem sub5868 (p : Pattern) : d78 (change p 141 none) = d78 p := by
  change (if p 182 then d36 (change p 141 none) else d35 (change p 141 none)) = d78 p
  rw [sub5848, sub5847]
  rfl
theorem sub5869 (p : Pattern) : d79 (change p 141 none) = d79 p := by
  change (if p 163 then d78 (change p 141 none) else d53 (change p 141 none)) = d79 p
  rw [sub5868, sub5867]
  rfl
theorem sub5870 (p : Pattern) : d62 (change p 141 none) = d62 p := by
  change (if p 182 then d41 (change p 141 none) else d40 (change p 141 none)) = d62 p
  rw [sub5854, sub5853]
  rfl
theorem sub5871 (p : Pattern) : d63 (change p 141 none) = d63 p := by
  change (if p 163 then d12 (change p 141 none) else d62 (change p 141 none)) = d63 p
  rw [sub5820, sub5870]
  rfl
theorem sub5872 (p : Pattern) : d80 (change p 141 none) = d80 p := by
  change (if p 162 then d63 (change p 141 none) else d79 (change p 141 none)) = d80 p
  rw [sub5871, sub5869]
  rfl
theorem sub5873 (p : Pattern) : d81 (change p 141 none) = d81 p := by
  change (if p 161 then d12 (change p 141 none) else d80 (change p 141 none)) = d81 p
  rw [sub5820, sub5872]
  rfl
theorem sub5874 (p : Pattern) : d82 (change p 141 none) = d82 p := by
  change (if p 160 then d81 (change p 141 none) else d29 (change p 141 none)) = d82 p
  rw [sub5873, sub5839]
  rfl
theorem sub5875 (p : Pattern) : d654 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5876 (p : Pattern) : d655 (change p 141 none) = d4797 p := by
  change (if p 138 then d654 (change p 141 none) else d653 (change p 141 none)) = d4797 p
  rw [sub5875, sub5866]
  rfl
theorem sub5877 (p : Pattern) : d656 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5878 (p : Pattern) : d89 (change p 141 none) = d89 p := by
  change (if p 163 then d62 (change p 141 none) else d26 (change p 141 none)) = d89 p
  rw [sub5870, sub5836]
  rfl
theorem sub5879 (p : Pattern) : d90 (change p 141 none) = d90 p := by
  change (if p 162 then d63 (change p 141 none) else d89 (change p 141 none)) = d90 p
  rw [sub5871, sub5878]
  rfl
end NetHack.Sokoban22Refined85
