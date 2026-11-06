/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5880 (p : Pattern) : d91 (change p 141 none) = d91 p := by
  change (if p 162 then d12 (change p 141 none) else d63 (change p 141 none)) = d91 p
  rw [sub5820, sub5871]
  rfl
theorem sub5881 (p : Pattern) : d92 (change p 141 none) = d92 p := by
  change (if p 161 then d91 (change p 141 none) else d90 (change p 141 none)) = d92 p
  rw [sub5880, sub5879]
  rfl
theorem sub5882 (p : Pattern) : d93 (change p 141 none) = d93 p := by
  change (if p 161 then d12 (change p 141 none) else d91 (change p 141 none)) = d93 p
  rw [sub5820, sub5880]
  rfl
theorem sub5883 (p : Pattern) : d94 (change p 141 none) = d94 p := by
  change (if p 160 then d93 (change p 141 none) else d92 (change p 141 none)) = d94 p
  rw [sub5882, sub5881]
  rfl
theorem sub5884 (p : Pattern) : d657 (change p 141 none) = d94 p := by
  change d94 (change p 141 none) = d94 p
  exact sub5883 p
theorem sub5885 (p : Pattern) : d658 (change p 141 none) = d4798 p := by
  change (if p 138 then d657 (change p 141 none) else d656 (change p 141 none)) = d4798 p
  rw [sub5884, sub5877]
  rfl
theorem sub5886 (p : Pattern) : d659 (change p 141 none) = d4799 p := by
  change (if p 116 then d658 (change p 141 none) else d655 (change p 141 none)) = d4799 p
  rw [sub5885, sub5876]
  rfl
theorem sub5887 (p : Pattern) : d660 (change p 141 none) = d52 p := by
  change d52 (change p 141 none) = d52 p
  exact sub5865 p
theorem sub5888 (p : Pattern) : d661 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5889 (p : Pattern) : d662 (change p 141 none) = d4797 p := by
  change (if p 138 then d661 (change p 141 none) else d660 (change p 141 none)) = d4797 p
  rw [sub5888, sub5887]
  rfl
theorem sub5890 (p : Pattern) : d663 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5891 (p : Pattern) : d664 (change p 141 none) = d4800 p := by
  change (if p 138 then d12 (change p 141 none) else d663 (change p 141 none)) = d4800 p
  rw [sub5820, sub5890]
  rfl
theorem sub5892 (p : Pattern) : d665 (change p 141 none) = d4801 p := by
  change (if p 116 then d664 (change p 141 none) else d662 (change p 141 none)) = d4801 p
  rw [sub5891, sub5889]
  rfl
theorem sub5893 (p : Pattern) : d666 (change p 141 none) = d4802 p := by
  change (if p 115 then d665 (change p 141 none) else d659 (change p 141 none)) = d4802 p
  rw [sub5892, sub5886]
  rfl
theorem sub5894 (p : Pattern) : d667 (change p 141 none) = d52 p := by
  change d52 (change p 141 none) = d52 p
  exact sub5865 p
theorem sub5895 (p : Pattern) : d668 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5896 (p : Pattern) : d669 (change p 141 none) = d4797 p := by
  change (if p 138 then d668 (change p 141 none) else d667 (change p 141 none)) = d4797 p
  rw [sub5895, sub5894]
  rfl
theorem sub5897 (p : Pattern) : d670 (change p 141 none) = d94 p := by
  change d94 (change p 141 none) = d94 p
  exact sub5883 p
theorem sub5898 (p : Pattern) : d671 (change p 141 none) = d4798 p := by
  change (if p 138 then d670 (change p 141 none) else d654 (change p 141 none)) = d4798 p
  rw [sub5897, sub5875]
  rfl
theorem sub5899 (p : Pattern) : d672 (change p 141 none) = d4799 p := by
  change (if p 116 then d671 (change p 141 none) else d669 (change p 141 none)) = d4799 p
  rw [sub5898, sub5896]
  rfl
theorem sub5900 (p : Pattern) : d673 (change p 141 none) = d52 p := by
  change d52 (change p 141 none) = d52 p
  exact sub5865 p
theorem sub5901 (p : Pattern) : d674 (change p 141 none) = d82 p := by
  change d82 (change p 141 none) = d82 p
  exact sub5874 p
theorem sub5902 (p : Pattern) : d675 (change p 141 none) = d4797 p := by
  change (if p 138 then d674 (change p 141 none) else d673 (change p 141 none)) = d4797 p
  rw [sub5901, sub5900]
  rfl
theorem sub5903 (p : Pattern) : d676 (change p 141 none) = d4800 p := by
  change (if p 138 then d12 (change p 141 none) else d661 (change p 141 none)) = d4800 p
  rw [sub5820, sub5888]
  rfl
theorem sub5904 (p : Pattern) : d677 (change p 141 none) = d4801 p := by
  change (if p 116 then d676 (change p 141 none) else d675 (change p 141 none)) = d4801 p
  rw [sub5903, sub5902]
  rfl
theorem sub5905 (p : Pattern) : d678 (change p 141 none) = d4802 p := by
  change (if p 115 then d677 (change p 141 none) else d672 (change p 141 none)) = d4802 p
  rw [sub5904, sub5899]
  rfl
theorem sub5906 (p : Pattern) : d679 (change p 141 none) = d4802 p := by
  change (if p 71 then d678 (change p 141 none) else d666 (change p 141 none)) = d4802 p
  rw [sub5905, sub5893]
  simp only [ite_self]
theorem sub5907 (p : Pattern) : d1 (change p 141 none) = d1 p := by
  rfl
theorem sub5908 (p : Pattern) : d102 (change p 141 none) = d102 p := by
  change (if p 247 then d12 (change p 141 none) else d1 (change p 141 none)) = d102 p
  rw [sub5820, sub5907]
  rfl
theorem sub5909 (p : Pattern) : d103 (change p 141 none) = d103 p := by
  change (if p 246 then d102 (change p 141 none) else d1 (change p 141 none)) = d103 p
  rw [sub5908, sub5907]
  rfl
theorem sub5910 (p : Pattern) : d104 (change p 141 none) = d104 p := by
  change (if p 204 then d12 (change p 141 none) else d103 (change p 141 none)) = d104 p
  rw [sub5820, sub5909]
  rfl
theorem sub5911 (p : Pattern) : d105 (change p 141 none) = d105 p := by
  change (if p 182 then d104 (change p 141 none) else d103 (change p 141 none)) = d105 p
  rw [sub5910, sub5909]
  rfl
theorem sub5912 (p : Pattern) : d5 (change p 141 none) = d5 p := by
  rfl
theorem sub5913 (p : Pattern) : d106 (change p 141 none) = d106 p := by
  change (if p 247 then d12 (change p 141 none) else d5 (change p 141 none)) = d106 p
  rw [sub5820, sub5912]
  rfl
theorem sub5914 (p : Pattern) : d107 (change p 141 none) = d107 p := by
  change (if p 246 then d106 (change p 141 none) else d5 (change p 141 none)) = d107 p
  rw [sub5913, sub5912]
  rfl
theorem sub5915 (p : Pattern) : d108 (change p 141 none) = d108 p := by
  change (if p 204 then d12 (change p 141 none) else d107 (change p 141 none)) = d108 p
  rw [sub5820, sub5914]
  rfl
theorem sub5916 (p : Pattern) : d109 (change p 141 none) = d109 p := by
  change (if p 182 then d108 (change p 141 none) else d107 (change p 141 none)) = d109 p
  rw [sub5915, sub5914]
  rfl
theorem sub5917 (p : Pattern) : d110 (change p 141 none) = d110 p := by
  change (if p 163 then d109 (change p 141 none) else d105 (change p 141 none)) = d110 p
  rw [sub5916, sub5911]
  rfl
theorem sub5918 (p : Pattern) : d111 (change p 141 none) = d111 p := by
  change (if p 162 then d110 (change p 141 none) else d105 (change p 141 none)) = d111 p
  rw [sub5917, sub5911]
  rfl
theorem sub5919 (p : Pattern) : d10 (change p 141 none) = d10 p := by
  rfl
theorem sub5920 (p : Pattern) : d57 (change p 141 none) = d57 p := by
  change (if p 247 then d12 (change p 141 none) else d10 (change p 141 none)) = d57 p
  rw [sub5820, sub5919]
  rfl
theorem sub5921 (p : Pattern) : d58 (change p 141 none) = d58 p := by
  change (if p 246 then d57 (change p 141 none) else d10 (change p 141 none)) = d58 p
  rw [sub5920, sub5919]
  rfl
theorem sub5922 (p : Pattern) : d59 (change p 141 none) = d59 p := by
  change (if p 204 then d12 (change p 141 none) else d58 (change p 141 none)) = d59 p
  rw [sub5820, sub5921]
  rfl
theorem sub5923 (p : Pattern) : d60 (change p 141 none) = d60 p := by
  change (if p 182 then d59 (change p 141 none) else d58 (change p 141 none)) = d60 p
  rw [sub5922, sub5921]
  rfl
theorem sub5924 (p : Pattern) : d112 (change p 141 none) = d112 p := by
  change (if p 163 then d12 (change p 141 none) else d60 (change p 141 none)) = d112 p
  rw [sub5820, sub5923]
  rfl
theorem sub5925 (p : Pattern) : d113 (change p 141 none) = d113 p := by
  change (if p 162 then d112 (change p 141 none) else d110 (change p 141 none)) = d113 p
  rw [sub5924, sub5917]
  rfl
theorem sub5926 (p : Pattern) : d114 (change p 141 none) = d114 p := by
  change (if p 161 then d113 (change p 141 none) else d111 (change p 141 none)) = d114 p
  rw [sub5925, sub5918]
  rfl
theorem sub5927 (p : Pattern) : d3 (change p 141 none) = d3 p := by
  rfl
theorem sub5928 (p : Pattern) : d115 (change p 141 none) = d115 p := by
  change (if p 247 then d12 (change p 141 none) else d3 (change p 141 none)) = d115 p
  rw [sub5820, sub5927]
  rfl
theorem sub5929 (p : Pattern) : d116 (change p 141 none) = d116 p := by
  change (if p 246 then d115 (change p 141 none) else d3 (change p 141 none)) = d116 p
  rw [sub5928, sub5927]
  rfl
theorem sub5930 (p : Pattern) : d117 (change p 141 none) = d117 p := by
  change (if p 204 then d12 (change p 141 none) else d116 (change p 141 none)) = d117 p
  rw [sub5820, sub5929]
  rfl
theorem sub5931 (p : Pattern) : d118 (change p 141 none) = d118 p := by
  change (if p 182 then d117 (change p 141 none) else d103 (change p 141 none)) = d118 p
  rw [sub5930, sub5909]
  rfl
theorem sub5932 (p : Pattern) : d7 (change p 141 none) = d7 p := by
  rfl
theorem sub5933 (p : Pattern) : d119 (change p 141 none) = d119 p := by
  change (if p 247 then d12 (change p 141 none) else d7 (change p 141 none)) = d119 p
  rw [sub5820, sub5932]
  rfl
theorem sub5934 (p : Pattern) : d120 (change p 141 none) = d120 p := by
  change (if p 246 then d119 (change p 141 none) else d7 (change p 141 none)) = d120 p
  rw [sub5933, sub5932]
  rfl
theorem sub5935 (p : Pattern) : d121 (change p 141 none) = d121 p := by
  change (if p 204 then d12 (change p 141 none) else d120 (change p 141 none)) = d121 p
  rw [sub5820, sub5934]
  rfl
theorem sub5936 (p : Pattern) : d122 (change p 141 none) = d122 p := by
  change (if p 182 then d121 (change p 141 none) else d103 (change p 141 none)) = d122 p
  rw [sub5935, sub5909]
  rfl
theorem sub5937 (p : Pattern) : d123 (change p 141 none) = d123 p := by
  change (if p 163 then d122 (change p 141 none) else d118 (change p 141 none)) = d123 p
  rw [sub5936, sub5931]
  rfl
theorem sub5938 (p : Pattern) : d124 (change p 141 none) = d124 p := by
  change (if p 182 then d12 (change p 141 none) else d103 (change p 141 none)) = d124 p
  rw [sub5820, sub5909]
  rfl
theorem sub5939 (p : Pattern) : d125 (change p 141 none) = d125 p := by
  change (if p 182 then d12 (change p 141 none) else d107 (change p 141 none)) = d125 p
  rw [sub5820, sub5914]
  rfl
theorem sub5940 (p : Pattern) : d126 (change p 141 none) = d126 p := by
  change (if p 163 then d125 (change p 141 none) else d124 (change p 141 none)) = d126 p
  rw [sub5939, sub5938]
  rfl
theorem sub5941 (p : Pattern) : d127 (change p 141 none) = d127 p := by
  change (if p 162 then d126 (change p 141 none) else d123 (change p 141 none)) = d127 p
  rw [sub5940, sub5937]
  rfl
theorem sub5942 (p : Pattern) : d70 (change p 141 none) = d70 p := by
  change (if p 182 then d12 (change p 141 none) else d58 (change p 141 none)) = d70 p
  rw [sub5820, sub5921]
  rfl
theorem sub5943 (p : Pattern) : d128 (change p 141 none) = d128 p := by
  change (if p 163 then d12 (change p 141 none) else d70 (change p 141 none)) = d128 p
  rw [sub5820, sub5942]
  rfl
theorem sub5944 (p : Pattern) : d129 (change p 141 none) = d129 p := by
  change (if p 162 then d128 (change p 141 none) else d126 (change p 141 none)) = d129 p
  rw [sub5943, sub5940]
  rfl
theorem sub5945 (p : Pattern) : d130 (change p 141 none) = d130 p := by
  change (if p 161 then d129 (change p 141 none) else d127 (change p 141 none)) = d130 p
  rw [sub5944, sub5941]
  rfl
theorem sub5946 (p : Pattern) : d131 (change p 141 none) = d131 p := by
  change (if p 160 then d130 (change p 141 none) else d114 (change p 141 none)) = d131 p
  rw [sub5945, sub5926]
  rfl
theorem sub5947 (p : Pattern) : d680 (change p 141 none) = d131 p := by
  change d131 (change p 141 none) = d131 p
  exact sub5946 p
theorem sub5948 (p : Pattern) : d132 (change p 141 none) = d132 p := by
  change (if p 182 then d117 (change p 141 none) else d116 (change p 141 none)) = d132 p
  rw [sub5930, sub5929]
  rfl
theorem sub5949 (p : Pattern) : d148 (change p 141 none) = d148 p := by
  change (if p 182 then d121 (change p 141 none) else d120 (change p 141 none)) = d148 p
  rw [sub5935, sub5934]
  rfl
theorem sub5950 (p : Pattern) : d149 (change p 141 none) = d149 p := by
  change (if p 163 then d148 (change p 141 none) else d132 (change p 141 none)) = d149 p
  rw [sub5949, sub5948]
  rfl
theorem sub5951 (p : Pattern) : d150 (change p 141 none) = d150 p := by
  change (if p 162 then d12 (change p 141 none) else d149 (change p 141 none)) = d150 p
  rw [sub5820, sub5950]
  rfl
theorem sub5952 (p : Pattern) : d151 (change p 141 none) = d151 p := by
  change (if p 161 then d12 (change p 141 none) else d150 (change p 141 none)) = d151 p
  rw [sub5820, sub5951]
  rfl
theorem sub5953 (p : Pattern) : d152 (change p 141 none) = d152 p := by
  change (if p 160 then d151 (change p 141 none) else d114 (change p 141 none)) = d152 p
  rw [sub5952, sub5926]
  rfl
theorem sub5954 (p : Pattern) : d681 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5955 (p : Pattern) : d682 (change p 141 none) = d4803 p := by
  change (if p 138 then d681 (change p 141 none) else d680 (change p 141 none)) = d4803 p
  rw [sub5954, sub5947]
  rfl
theorem sub5956 (p : Pattern) : d683 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5957 (p : Pattern) : d159 (change p 141 none) = d159 p := by
  change (if p 162 then d12 (change p 141 none) else d112 (change p 141 none)) = d159 p
  rw [sub5820, sub5924]
  rfl
theorem sub5958 (p : Pattern) : d160 (change p 141 none) = d160 p := by
  change (if p 161 then d12 (change p 141 none) else d159 (change p 141 none)) = d160 p
  rw [sub5820, sub5957]
  rfl
theorem sub5959 (p : Pattern) : d161 (change p 141 none) = d161 p := by
  change (if p 160 then d12 (change p 141 none) else d160 (change p 141 none)) = d161 p
  rw [sub5820, sub5958]
  rfl
theorem sub5960 (p : Pattern) : d162 (change p 141 none) = d161 p := by
  change d161 (change p 141 none) = d161 p
  exact sub5959 p
theorem sub5961 (p : Pattern) : d684 (change p 141 none) = d4804 p := by
  change (if p 138 then d162 (change p 141 none) else d683 (change p 141 none)) = d4804 p
  rw [sub5960, sub5956]
  rfl
theorem sub5962 (p : Pattern) : d685 (change p 141 none) = d4805 p := by
  change (if p 116 then d684 (change p 141 none) else d682 (change p 141 none)) = d4805 p
  rw [sub5961, sub5955]
  rfl
theorem sub5963 (p : Pattern) : d686 (change p 141 none) = d131 p := by
  change d131 (change p 141 none) = d131 p
  exact sub5946 p
theorem sub5964 (p : Pattern) : d687 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5965 (p : Pattern) : d688 (change p 141 none) = d4803 p := by
  change (if p 138 then d687 (change p 141 none) else d686 (change p 141 none)) = d4803 p
  rw [sub5964, sub5963]
  rfl
theorem sub5966 (p : Pattern) : d689 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5967 (p : Pattern) : d690 (change p 141 none) = d4806 p := by
  change (if p 138 then d12 (change p 141 none) else d689 (change p 141 none)) = d4806 p
  rw [sub5820, sub5966]
  rfl
theorem sub5968 (p : Pattern) : d691 (change p 141 none) = d4807 p := by
  change (if p 116 then d690 (change p 141 none) else d688 (change p 141 none)) = d4807 p
  rw [sub5967, sub5965]
  rfl
theorem sub5969 (p : Pattern) : d692 (change p 141 none) = d4808 p := by
  change (if p 115 then d691 (change p 141 none) else d685 (change p 141 none)) = d4808 p
  rw [sub5968, sub5962]
  rfl
theorem sub5970 (p : Pattern) : d693 (change p 141 none) = d4809 p := by
  change (if p 71 then d692 (change p 141 none) else d666 (change p 141 none)) = d4809 p
  rw [sub5969, sub5893]
  rfl
theorem sub5971 (p : Pattern) : d694 (change p 141 none) = d4810 p := by
  change (if p 49 then d693 (change p 141 none) else d679 (change p 141 none)) = d4810 p
  rw [sub5970, sub5906]
  rfl
theorem sub5972 (p : Pattern) : d695 (change p 141 none) = d131 p := by
  change d131 (change p 141 none) = d131 p
  exact sub5946 p
theorem sub5973 (p : Pattern) : d696 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5974 (p : Pattern) : d697 (change p 141 none) = d4803 p := by
  change (if p 138 then d696 (change p 141 none) else d695 (change p 141 none)) = d4803 p
  rw [sub5973, sub5972]
  rfl
theorem sub5975 (p : Pattern) : d698 (change p 141 none) = d152 p := by
  change d152 (change p 141 none) = d152 p
  exact sub5953 p
theorem sub5976 (p : Pattern) : d699 (change p 141 none) = d4804 p := by
  change (if p 138 then d162 (change p 141 none) else d698 (change p 141 none)) = d4804 p
  rw [sub5960, sub5975]
  rfl
theorem sub5977 (p : Pattern) : d700 (change p 141 none) = d4805 p := by
  change (if p 116 then d699 (change p 141 none) else d697 (change p 141 none)) = d4805 p
  rw [sub5976, sub5974]
  rfl
theorem sub5978 (p : Pattern) : d268 (change p 141 none) = d268 p := by
  change (if p 204 then d116 (change p 141 none) else d103 (change p 141 none)) = d268 p
  rw [sub5929, sub5909]
  rfl
theorem sub5979 (p : Pattern) : d269 (change p 141 none) = d269 p := by
  change (if p 182 then d117 (change p 141 none) else d268 (change p 141 none)) = d269 p
  rw [sub5930, sub5978]
  rfl
theorem sub5980 (p : Pattern) : d270 (change p 141 none) = d270 p := by
  change (if p 182 then d121 (change p 141 none) else d268 (change p 141 none)) = d270 p
  rw [sub5935, sub5978]
  rfl
theorem sub5981 (p : Pattern) : d271 (change p 141 none) = d271 p := by
  change (if p 163 then d270 (change p 141 none) else d269 (change p 141 none)) = d271 p
  rw [sub5980, sub5979]
  rfl
theorem sub5982 (p : Pattern) : d272 (change p 141 none) = d272 p := by
  change (if p 182 then d12 (change p 141 none) else d268 (change p 141 none)) = d272 p
  rw [sub5820, sub5978]
  rfl
theorem sub5983 (p : Pattern) : d273 (change p 141 none) = d273 p := by
  change (if p 204 then d120 (change p 141 none) else d107 (change p 141 none)) = d273 p
  rw [sub5934, sub5914]
  rfl
theorem sub5984 (p : Pattern) : d274 (change p 141 none) = d274 p := by
  change (if p 182 then d12 (change p 141 none) else d273 (change p 141 none)) = d274 p
  rw [sub5820, sub5983]
  rfl
theorem sub5985 (p : Pattern) : d275 (change p 141 none) = d275 p := by
  change (if p 163 then d274 (change p 141 none) else d272 (change p 141 none)) = d275 p
  rw [sub5984, sub5982]
  rfl
theorem sub5986 (p : Pattern) : d276 (change p 141 none) = d276 p := by
  change (if p 162 then d275 (change p 141 none) else d271 (change p 141 none)) = d276 p
  rw [sub5985, sub5981]
  rfl
theorem sub5987 (p : Pattern) : d277 (change p 141 none) = d277 p := by
  change (if p 182 then d12 (change p 141 none) else d59 (change p 141 none)) = d277 p
  rw [sub5820, sub5922]
  rfl
theorem sub5988 (p : Pattern) : d278 (change p 141 none) = d278 p := by
  change (if p 163 then d12 (change p 141 none) else d277 (change p 141 none)) = d278 p
  rw [sub5820, sub5987]
  rfl
theorem sub5989 (p : Pattern) : d279 (change p 141 none) = d279 p := by
  change (if p 162 then d278 (change p 141 none) else d275 (change p 141 none)) = d279 p
  rw [sub5988, sub5985]
  rfl
theorem sub5990 (p : Pattern) : d280 (change p 141 none) = d280 p := by
  change (if p 161 then d279 (change p 141 none) else d276 (change p 141 none)) = d280 p
  rw [sub5989, sub5986]
  rfl
theorem sub5991 (p : Pattern) : d281 (change p 141 none) = d281 p := by
  change (if p 160 then d280 (change p 141 none) else d114 (change p 141 none)) = d281 p
  rw [sub5990, sub5926]
  rfl
theorem sub5992 (p : Pattern) : d701 (change p 141 none) = d281 p := by
  change d281 (change p 141 none) = d281 p
  exact sub5991 p
theorem sub5993 (p : Pattern) : d291 (change p 141 none) = d291 p := by
  change (if p 163 then d269 (change p 141 none) else d105 (change p 141 none)) = d291 p
  rw [sub5979, sub5911]
  rfl
theorem sub5994 (p : Pattern) : d292 (change p 141 none) = d292 p := by
  change (if p 182 then d121 (change p 141 none) else d273 (change p 141 none)) = d292 p
  rw [sub5935, sub5983]
  rfl
theorem sub5995 (p : Pattern) : d293 (change p 141 none) = d293 p := by
  change (if p 163 then d292 (change p 141 none) else d269 (change p 141 none)) = d293 p
  rw [sub5994, sub5979]
  rfl
theorem sub5996 (p : Pattern) : d294 (change p 141 none) = d294 p := by
  change (if p 162 then d293 (change p 141 none) else d291 (change p 141 none)) = d294 p
  rw [sub5995, sub5993]
  rfl
theorem sub5997 (p : Pattern) : d295 (change p 141 none) = d295 p := by
  change (if p 162 then d278 (change p 141 none) else d293 (change p 141 none)) = d295 p
  rw [sub5988, sub5995]
  rfl
theorem sub5998 (p : Pattern) : d296 (change p 141 none) = d296 p := by
  change (if p 161 then d295 (change p 141 none) else d294 (change p 141 none)) = d296 p
  rw [sub5997, sub5996]
  rfl
theorem sub5999 (p : Pattern) : d297 (change p 141 none) = d297 p := by
  change (if p 160 then d151 (change p 141 none) else d296 (change p 141 none)) = d297 p
  rw [sub5952, sub5998]
  rfl
end NetHack.Sokoban22Refined85
