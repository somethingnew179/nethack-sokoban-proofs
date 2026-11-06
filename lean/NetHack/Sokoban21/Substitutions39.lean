/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions38
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5850 (pattern : Twelve) : d130 (change pattern 1 12) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 1 12) else d121 (change pattern 1 12)) = d130 pattern
  rw [s5481, s5849]
  rfl
theorem s5851 (pattern : Twelve) : d137 (change pattern 1 12) = d137 pattern := by
  change (if pattern.f then d130 (change pattern 1 12) else d52 (change pattern 1 12)) = d137 pattern
  rw [s5850, s5779]
  rfl
theorem s5852 (pattern : Twelve) : d138 (change pattern 1 12) = d138 pattern := by
  change (if pattern.f then d129 (change pattern 1 12) else d56 (change pattern 1 12)) = d138 pattern
  rw [s5846, s5474]
  rfl
theorem s5853 (pattern : Twelve) : d145 (change pattern 1 12) = d145 pattern := by
  change (if pattern.e then d138 (change pattern 1 12) else d137 (change pattern 1 12)) = d145 pattern
  rw [s5852, s5851]
  rfl
theorem s5854 (pattern : Twelve) : d149 (change pattern 1 12) = d149 pattern := by
  change (if pattern.j then d145 (change pattern 1 12) else d144 (change pattern 1 12)) = d149 pattern
  rw [s5853, s5848]
  rfl
theorem s5855 (pattern : Twelve) : d139 (change pattern 1 12) = d139 pattern := by
  change (if pattern.f then d130 (change pattern 1 12) else d56 (change pattern 1 12)) = d139 pattern
  rw [s5850, s5474]
  rfl
theorem s5856 (pattern : Twelve) : d146 (change pattern 1 12) = d146 pattern := by
  change (if pattern.e then d138 (change pattern 1 12) else d139 (change pattern 1 12)) = d146 pattern
  rw [s5852, s5855]
  rfl
theorem s5857 (pattern : Twelve) : d150 (change pattern 1 12) = d150 pattern := by
  change (if pattern.j then d146 (change pattern 1 12) else d144 (change pattern 1 12)) = d150 pattern
  rw [s5856, s5848]
  rfl
theorem s5858 (pattern : Twelve) : d153 (change pattern 1 12) = d153 pattern := by
  change (if pattern.d then d150 (change pattern 1 12) else d149 (change pattern 1 12)) = d153 pattern
  rw [s5857, s5854]
  rfl
theorem s5859 (pattern : Twelve) : d122 (change pattern 1 12) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 1 12) else d17 (change pattern 1 12)) = d122 pattern
  rw [s5461, s5450]
  rfl
theorem s5860 (pattern : Twelve) : d131 (change pattern 1 12) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 1 12) else d121 (change pattern 1 12)) = d131 pattern
  rw [s5859, s5849]
  rfl
theorem s5861 (pattern : Twelve) : d140 (change pattern 1 12) = d140 pattern := by
  change (if pattern.f then d131 (change pattern 1 12) else d30 (change pattern 1 12)) = d140 pattern
  rw [s5860, s5472]
  rfl
theorem s5862 (pattern : Twelve) : d123 (change pattern 1 12) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d0 (change pattern 1 12)) = d123 pattern
  rw [s5458, s5447]
  rfl
theorem s5863 (pattern : Twelve) : d132 (change pattern 1 12) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 1 12) else d30 (change pattern 1 12)) = d132 pattern
  rw [s5862, s5472]
  rfl
theorem s5864 (pattern : Twelve) : d141 (change pattern 1 12) = d141 pattern := by
  change (if pattern.f then d129 (change pattern 1 12) else d132 (change pattern 1 12)) = d141 pattern
  rw [s5846, s5863]
  rfl
theorem s5865 (pattern : Twelve) : d147 (change pattern 1 12) = d147 pattern := by
  change (if pattern.e then d141 (change pattern 1 12) else d140 (change pattern 1 12)) = d147 pattern
  rw [s5864, s5861]
  rfl
theorem s5866 (pattern : Twelve) : d124 (change pattern 1 12) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 1 12) else d2 (change pattern 1 12)) = d124 pattern
  rw [s5575, s5456]
  rfl
theorem s5867 (pattern : Twelve) : d133 (change pattern 1 12) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 1 12) else d124 (change pattern 1 12)) = d133 pattern
  rw [s5577, s5866]
  rfl
theorem s5868 (pattern : Twelve) : d142 (change pattern 1 12) = d142 pattern := by
  change (if pattern.f then d133 (change pattern 1 12) else d59 (change pattern 1 12)) = d142 pattern
  rw [s5867, s5493]
  rfl
theorem s5869 (pattern : Twelve) : d126 (change pattern 1 12) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 1 12) else d2 (change pattern 1 12)) = d126 pattern
  rw [s5463, s5456]
  rfl
theorem s5870 (pattern : Twelve) : d134 (change pattern 1 12) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 1 12) else d126 (change pattern 1 12)) = d134 pattern
  rw [s5531, s5869]
  rfl
theorem s5871 (pattern : Twelve) : d135 (change pattern 1 12) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 1 12) else d127 (change pattern 1 12)) = d135 pattern
  rw [s5688, s5570]
  rfl
theorem s5872 (pattern : Twelve) : d143 (change pattern 1 12) = d143 pattern := by
  change (if pattern.f then d135 (change pattern 1 12) else d134 (change pattern 1 12)) = d143 pattern
  rw [s5871, s5870]
  rfl
theorem s5873 (pattern : Twelve) : d148 (change pattern 1 12) = d148 pattern := by
  change (if pattern.e then d143 (change pattern 1 12) else d142 (change pattern 1 12)) = d148 pattern
  rw [s5872, s5868]
  rfl
theorem s5874 (pattern : Twelve) : d151 (change pattern 1 12) = d151 pattern := by
  change (if pattern.j then d148 (change pattern 1 12) else d147 (change pattern 1 12)) = d151 pattern
  rw [s5873, s5865]
  rfl
theorem s5875 (pattern : Twelve) : d152 (change pattern 1 12) = d152 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d146 (change pattern 1 12)) = d152 pattern
  rw [s5467, s5856]
  rfl
theorem s5876 (pattern : Twelve) : d154 (change pattern 1 12) = d154 pattern := by
  change (if pattern.d then d152 (change pattern 1 12) else d151 (change pattern 1 12)) = d154 pattern
  rw [s5875, s5874]
  rfl
theorem s5877 (pattern : Twelve) : d155 (change pattern 1 12) = d155 pattern := by
  change (if pattern.c then d154 (change pattern 1 12) else d153 (change pattern 1 12)) = d155 pattern
  rw [s5876, s5858]
  rfl
theorem s5878 (pattern : Twelve) : d778 (change pattern 1 12) = d778 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d2 (change pattern 1 12)) = d778 pattern
  rw [s5458, s5456]
  rfl
theorem s5879 (pattern : Twelve) : d782 (change pattern 1 12) = d782 pattern := by
  change (if pattern.h then d779 (change pattern 1 12) else d778 (change pattern 1 12)) = d782 pattern
  rw [s5586, s5878]
  rfl
theorem s5880 (pattern : Twelve) : d788 (change pattern 1 12) = d788 pattern := by
  change (if pattern.f then d782 (change pattern 1 12) else d2 (change pattern 1 12)) = d788 pattern
  rw [s5879, s5456]
  rfl
theorem s5881 (pattern : Twelve) : d789 (change pattern 1 12) = d789 pattern := by
  change (if pattern.f then d61 (change pattern 1 12) else d38 (change pattern 1 12)) = d789 pattern
  rw [s5804, s5491]
  rfl
theorem s5882 (pattern : Twelve) : d794 (change pattern 1 12) = d794 pattern := by
  change (if pattern.e then d789 (change pattern 1 12) else d788 (change pattern 1 12)) = d794 pattern
  rw [s5881, s5880]
  rfl
theorem s5883 (pattern : Twelve) : d783 (change pattern 1 12) = d783 pattern := by
  change (if pattern.h then d44 (change pattern 1 12) else d38 (change pattern 1 12)) = d783 pattern
  rw [s5815, s5491]
  rfl
theorem s5884 (pattern : Twelve) : d790 (change pattern 1 12) = d790 pattern := by
  change (if pattern.f then d69 (change pattern 1 12) else d783 (change pattern 1 12)) = d790 pattern
  rw [s5833, s5883]
  rfl
theorem s5885 (pattern : Twelve) : d795 (change pattern 1 12) = d795 pattern := by
  change (if pattern.e then d90 (change pattern 1 12) else d790 (change pattern 1 12)) = d795 pattern
  rw [s5837, s5884]
  rfl
theorem s5886 (pattern : Twelve) : d798 (change pattern 1 12) = d798 pattern := by
  change (if pattern.j then d795 (change pattern 1 12) else d794 (change pattern 1 12)) = d798 pattern
  rw [s5885, s5882]
  rfl
theorem s5887 (pattern : Twelve) : d799 (change pattern 1 12) = d799 pattern := by
  change (if pattern.j then d101 (change pattern 1 12) else d794 (change pattern 1 12)) = d799 pattern
  rw [s5838, s5882]
  rfl
theorem s5888 (pattern : Twelve) : d802 (change pattern 1 12) = d802 pattern := by
  change (if pattern.d then d799 (change pattern 1 12) else d798 (change pattern 1 12)) = d802 pattern
  rw [s5887, s5886]
  rfl
theorem s5889 (pattern : Twelve) : d784 (change pattern 1 12) = d784 pattern := by
  change (if pattern.h then d780 (change pattern 1 12) else d38 (change pattern 1 12)) = d784 pattern
  rw [s5594, s5491]
  rfl
theorem s5890 (pattern : Twelve) : d791 (change pattern 1 12) = d791 pattern := by
  change (if pattern.f then d784 (change pattern 1 12) else d38 (change pattern 1 12)) = d791 pattern
  rw [s5889, s5491]
  rfl
theorem s5891 (pattern : Twelve) : d796 (change pattern 1 12) = d796 pattern := by
  change (if pattern.e then d90 (change pattern 1 12) else d791 (change pattern 1 12)) = d796 pattern
  rw [s5837, s5890]
  rfl
theorem s5892 (pattern : Twelve) : d785 (change pattern 1 12) = d785 pattern := by
  change (if pattern.h then d781 (change pattern 1 12) else d48 (change pattern 1 12)) = d785 pattern
  rw [s5599, s5534]
  rfl
theorem s5893 (pattern : Twelve) : d792 (change pattern 1 12) = d792 pattern := by
  change (if pattern.f then d785 (change pattern 1 12) else d48 (change pattern 1 12)) = d792 pattern
  rw [s5892, s5534]
  rfl
theorem s5894 (pattern : Twelve) : d786 (change pattern 1 12) = d786 pattern := by
  change (if pattern.h then d6 (change pattern 1 12) else d48 (change pattern 1 12)) = d786 pattern
  rw [s5467, s5534]
  rfl
theorem s5895 (pattern : Twelve) : d793 (change pattern 1 12) = d793 pattern := by
  change (if pattern.f then d787 (change pattern 1 12) else d786 (change pattern 1 12)) = d793 pattern
  rw [s5602, s5894]
  rfl
theorem s5896 (pattern : Twelve) : d797 (change pattern 1 12) = d797 pattern := by
  change (if pattern.e then d793 (change pattern 1 12) else d792 (change pattern 1 12)) = d797 pattern
  rw [s5895, s5893]
  rfl
theorem s5897 (pattern : Twelve) : d800 (change pattern 1 12) = d800 pattern := by
  change (if pattern.j then d797 (change pattern 1 12) else d796 (change pattern 1 12)) = d800 pattern
  rw [s5896, s5891]
  rfl
theorem s5898 (pattern : Twelve) : d801 (change pattern 1 12) = d801 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d101 (change pattern 1 12)) = d801 pattern
  rw [s5467, s5838]
  rfl
theorem s5899 (pattern : Twelve) : d803 (change pattern 1 12) = d803 pattern := by
  change (if pattern.d then d801 (change pattern 1 12) else d800 (change pattern 1 12)) = d803 pattern
  rw [s5898, s5897]
  rfl
theorem s5900 (pattern : Twelve) : d804 (change pattern 1 12) = d804 pattern := by
  change (if pattern.c then d803 (change pattern 1 12) else d802 (change pattern 1 12)) = d804 pattern
  rw [s5899, s5888]
  rfl
theorem s5901 (pattern : Twelve) : d805 (change pattern 1 12) = d805 pattern := by
  change (if pattern.g then d804 (change pattern 1 12) else d155 (change pattern 1 12)) = d805 pattern
  rw [s5900, s5877]
  rfl
theorem s5902 (pattern : Twelve) : d811 (change pattern 1 12) = d805 pattern := by
  change d805 (change pattern 1 12) = d805 pattern
  exact s5901 pattern
theorem s5903 (pattern : Twelve) : d812 (change pattern 1 12) = d806 pattern := by
  change (if pattern.a then d811 (change pattern 1 12) else d810 (change pattern 1 12)) = d806 pattern
  rw [s5902, s5844]
  rfl
theorem s5904 (pattern : Twelve) : d0 (change pattern 12 6) = d0 pattern := by
  rfl
theorem s5905 (pattern : Twelve) : d1 (change pattern 12 6) = d1 pattern := by
  rfl
theorem s5906 (pattern : Twelve) : d26 (change pattern 12 6) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 6) else d0 (change pattern 12 6)) = d26 pattern
  rw [s5905, s5904]
  rfl
theorem s5907 (pattern : Twelve) : d7 (change pattern 12 6) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 6) else d0 (change pattern 12 6)) = d7 pattern
  rw [s5905, s5904]
  rfl
theorem s5908 (pattern : Twelve) : d17 (change pattern 12 6) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 6) else d0 (change pattern 12 6)) = d17 pattern
  rw [s5907, s5904]
  rfl
theorem s5909 (pattern : Twelve) : d27 (change pattern 12 6) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 6) else d17 (change pattern 12 6)) = d27 pattern
  rw [s5905, s5908]
  rfl
theorem s5910 (pattern : Twelve) : d50 (change pattern 12 6) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 6) else d26 (change pattern 12 6)) = d50 pattern
  rw [s5909, s5906]
  rfl
theorem s5911 (pattern : Twelve) : d72 (change pattern 12 6) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 12 6) else d0 (change pattern 12 6)) = d72 pattern
  rw [s5910, s5904]
  rfl
theorem s5912 (pattern : Twelve) : d2 (change pattern 12 6) = d2 pattern := by
  rfl
theorem s5913 (pattern : Twelve) : d30 (change pattern 12 6) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 6) else d0 (change pattern 12 6)) = d30 pattern
  rw [s5912, s5904]
  rfl
theorem s5914 (pattern : Twelve) : d3 (change pattern 12 6) = d3 pattern := by
  rfl
theorem s5915 (pattern : Twelve) : d9 (change pattern 12 6) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 6) else d2 (change pattern 12 6)) = d9 pattern
  rw [s5914, s5912]
  rfl
theorem s5916 (pattern : Twelve) : d23 (change pattern 12 6) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 6) else d2 (change pattern 12 6)) = d23 pattern
  rw [s5915, s5912]
  rfl
theorem s5917 (pattern : Twelve) : d34 (change pattern 12 6) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 6) else d17 (change pattern 12 6)) = d34 pattern
  rw [s5916, s5908]
  rfl
theorem s5918 (pattern : Twelve) : d10 (change pattern 12 6) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 6) else d0 (change pattern 12 6)) = d10 pattern
  rw [s5912, s5904]
  rfl
theorem s5919 (pattern : Twelve) : d11 (change pattern 12 6) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 6) else d1 (change pattern 12 6)) = d11 pattern
  rw [s5914, s5905]
  rfl
theorem s5920 (pattern : Twelve) : d19 (change pattern 12 6) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 6) else d10 (change pattern 12 6)) = d19 pattern
  rw [s5919, s5918]
  rfl
theorem s5921 (pattern : Twelve) : d6 (change pattern 12 6) = d6 pattern := by
  rfl
theorem s5922 (pattern : Twelve) : d29 (change pattern 12 6) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d19 (change pattern 12 6)) = d29 pattern
  rw [s5921, s5920]
  rfl
theorem s5923 (pattern : Twelve) : d55 (change pattern 12 6) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 6) else d34 (change pattern 12 6)) = d55 pattern
  rw [s5922, s5917]
  rfl
theorem s5924 (pattern : Twelve) : d80 (change pattern 12 6) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 12 6) else d30 (change pattern 12 6)) = d80 pattern
  rw [s5923, s5913]
  rfl
theorem s5925 (pattern : Twelve) : d97 (change pattern 12 6) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 12 6) else d72 (change pattern 12 6)) = d97 pattern
  rw [s5924, s5911]
  rfl
theorem s5926 (pattern : Twelve) : d5 (change pattern 12 6) = d5 pattern := by
  rfl
theorem s5927 (pattern : Twelve) : d12 (change pattern 12 6) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 6) else d3 (change pattern 12 6)) = d12 pattern
  rw [s5926, s5914]
  rfl
theorem s5928 (pattern : Twelve) : d4 (change pattern 12 6) = d4 pattern := by
  rfl
theorem s5929 (pattern : Twelve) : d13 (change pattern 12 6) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 6) else d4 (change pattern 12 6)) = d13 pattern
  rw [s5921, s5928]
  rfl
theorem s5930 (pattern : Twelve) : d20 (change pattern 12 6) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 6) else d12 (change pattern 12 6)) = d20 pattern
  rw [s5929, s5927]
  rfl
theorem s5931 (pattern : Twelve) : d31 (change pattern 12 6) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 12 6) else d0 (change pattern 12 6)) = d31 pattern
  rw [s5930, s5904]
  rfl
theorem s5932 (pattern : Twelve) : d52 (change pattern 12 6) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 12 6) else d30 (change pattern 12 6)) = d52 pattern
  rw [s5931, s5913]
  rfl
theorem s5933 (pattern : Twelve) : d14 (change pattern 12 6) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 6) else d5 (change pattern 12 6)) = d14 pattern
  rw [s5921, s5926]
  rfl
theorem s5934 (pattern : Twelve) : d21 (change pattern 12 6) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 6) else d13 (change pattern 12 6)) = d21 pattern
  rw [s5933, s5929]
  rfl
theorem s5935 (pattern : Twelve) : d43 (change pattern 12 6) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 12 6) else d1 (change pattern 12 6)) = d43 pattern
  rw [s5934, s5905]
  rfl
theorem s5936 (pattern : Twelve) : d62 (change pattern 12 6) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 12 6) else d30 (change pattern 12 6)) = d62 pattern
  rw [s5935, s5913]
  rfl
theorem s5937 (pattern : Twelve) : d83 (change pattern 12 6) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 12 6) else d52 (change pattern 12 6)) = d83 pattern
  rw [s5936, s5932]
  rfl
theorem s5938 (pattern : Twelve) : d22 (change pattern 12 6) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 6) else d14 (change pattern 12 6)) = d22 pattern
  rw [s5921, s5933]
  rfl
theorem s5939 (pattern : Twelve) : d44 (change pattern 12 6) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 12 6) else d2 (change pattern 12 6)) = d44 pattern
  rw [s5938, s5912]
  rfl
theorem s5940 (pattern : Twelve) : d63 (change pattern 12 6) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 12 6) else d30 (change pattern 12 6)) = d63 pattern
  rw [s5939, s5913]
  rfl
theorem s5941 (pattern : Twelve) : d40 (change pattern 12 6) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d23 (change pattern 12 6)) = d40 pattern
  rw [s5921, s5916]
  rfl
theorem s5942 (pattern : Twelve) : d64 (change pattern 12 6) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 12 6) else d34 (change pattern 12 6)) = d64 pattern
  rw [s5941, s5917]
  rfl
theorem s5943 (pattern : Twelve) : d84 (change pattern 12 6) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 12 6) else d63 (change pattern 12 6)) = d84 pattern
  rw [s5942, s5940]
  rfl
theorem s5944 (pattern : Twelve) : d98 (change pattern 12 6) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 12 6) else d83 (change pattern 12 6)) = d98 pattern
  rw [s5943, s5937]
  rfl
theorem s5945 (pattern : Twelve) : d106 (change pattern 12 6) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 12 6) else d97 (change pattern 12 6)) = d106 pattern
  rw [s5944, s5925]
  rfl
theorem s5946 (pattern : Twelve) : d35 (change pattern 12 6) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d0 (change pattern 12 6)) = d35 pattern
  rw [s5921, s5904]
  rfl
theorem s5947 (pattern : Twelve) : d56 (change pattern 12 6) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 6) else d30 (change pattern 12 6)) = d56 pattern
  rw [s5946, s5913]
  rfl
theorem s5948 (pattern : Twelve) : d45 (change pattern 12 6) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d1 (change pattern 12 6)) = d45 pattern
  rw [s5921, s5905]
  rfl
theorem s5949 (pattern : Twelve) : d65 (change pattern 12 6) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 12 6) else d30 (change pattern 12 6)) = d65 pattern
  rw [s5948, s5913]
  rfl
theorem s5950 (pattern : Twelve) : d85 (change pattern 12 6) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 12 6) else d56 (change pattern 12 6)) = d85 pattern
  rw [s5949, s5947]
  rfl
theorem s5951 (pattern : Twelve) : d39 (change pattern 12 6) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d2 (change pattern 12 6)) = d39 pattern
  rw [s5921, s5912]
  rfl
theorem s5952 (pattern : Twelve) : d66 (change pattern 12 6) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 12 6) else d30 (change pattern 12 6)) = d66 pattern
  rw [s5951, s5913]
  rfl
theorem s5953 (pattern : Twelve) : d86 (change pattern 12 6) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 12 6) else d66 (change pattern 12 6)) = d86 pattern
  rw [s5942, s5952]
  rfl
theorem s5954 (pattern : Twelve) : d99 (change pattern 12 6) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 12 6) else d85 (change pattern 12 6)) = d99 pattern
  rw [s5953, s5950]
  rfl
theorem s5955 (pattern : Twelve) : d107 (change pattern 12 6) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 12 6) else d97 (change pattern 12 6)) = d107 pattern
  rw [s5954, s5925]
  rfl
theorem s5956 (pattern : Twelve) : d112 (change pattern 12 6) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 12 6) else d106 (change pattern 12 6)) = d112 pattern
  rw [s5955, s5945]
  rfl
theorem s5957 (pattern : Twelve) : d46 (change pattern 12 6) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 12 6) else d1 (change pattern 12 6)) = d46 pattern
  rw [s5914, s5905]
  rfl
theorem s5958 (pattern : Twelve) : d67 (change pattern 12 6) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 12 6) else d30 (change pattern 12 6)) = d67 pattern
  rw [s5957, s5913]
  rfl
theorem s5959 (pattern : Twelve) : d87 (change pattern 12 6) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 12 6) else d30 (change pattern 12 6)) = d87 pattern
  rw [s5958, s5913]
  rfl
theorem s5960 (pattern : Twelve) : d38 (change pattern 12 6) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 6) else d2 (change pattern 12 6)) = d38 pattern
  rw [s5928, s5912]
  rfl
theorem s5961 (pattern : Twelve) : d68 (change pattern 12 6) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 12 6) else d30 (change pattern 12 6)) = d68 pattern
  rw [s5960, s5913]
  rfl
theorem s5962 (pattern : Twelve) : d88 (change pattern 12 6) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 12 6) else d68 (change pattern 12 6)) = d88 pattern
  rw [s5942, s5961]
  rfl
theorem s5963 (pattern : Twelve) : d100 (change pattern 12 6) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 12 6) else d87 (change pattern 12 6)) = d100 pattern
  rw [s5962, s5959]
  rfl
theorem s5964 (pattern : Twelve) : d59 (change pattern 12 6) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 12 6) else d38 (change pattern 12 6)) = d59 pattern
  rw [s5951, s5960]
  rfl
theorem s5965 (pattern : Twelve) : d47 (change pattern 12 6) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d3 (change pattern 12 6)) = d47 pattern
  rw [s5921, s5914]
  rfl
theorem s5966 (pattern : Twelve) : d69 (change pattern 12 6) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 12 6) else d38 (change pattern 12 6)) = d69 pattern
  rw [s5965, s5960]
  rfl
theorem s5967 (pattern : Twelve) : d89 (change pattern 12 6) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 12 6) else d59 (change pattern 12 6)) = d89 pattern
  rw [s5966, s5964]
  rfl
theorem s5968 (pattern : Twelve) : d48 (change pattern 12 6) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d4 (change pattern 12 6)) = d48 pattern
  rw [s5921, s5928]
  rfl
theorem s5969 (pattern : Twelve) : d70 (change pattern 12 6) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 12 6) else d38 (change pattern 12 6)) = d70 pattern
  rw [s5968, s5960]
  rfl
theorem s5970 (pattern : Twelve) : d15 (change pattern 12 6) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 6) else d4 (change pattern 12 6)) = d15 pattern
  rw [s5926, s5928]
  rfl
theorem s5971 (pattern : Twelve) : d24 (change pattern 12 6) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 6) else d4 (change pattern 12 6)) = d24 pattern
  rw [s5970, s5928]
  rfl
theorem s5972 (pattern : Twelve) : d41 (change pattern 12 6) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 12 6) else d23 (change pattern 12 6)) = d41 pattern
  rw [s5971, s5916]
  rfl
theorem s5973 (pattern : Twelve) : d49 (change pattern 12 6) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d24 (change pattern 12 6)) = d49 pattern
  rw [s5921, s5971]
  rfl
theorem s5974 (pattern : Twelve) : d71 (change pattern 12 6) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 12 6) else d41 (change pattern 12 6)) = d71 pattern
  rw [s5973, s5972]
  rfl
theorem s5975 (pattern : Twelve) : d90 (change pattern 12 6) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 12 6) else d70 (change pattern 12 6)) = d90 pattern
  rw [s5974, s5969]
  rfl
theorem s5976 (pattern : Twelve) : d101 (change pattern 12 6) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 12 6) else d89 (change pattern 12 6)) = d101 pattern
  rw [s5975, s5967]
  rfl
theorem s5977 (pattern : Twelve) : d108 (change pattern 12 6) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 12 6) else d100 (change pattern 12 6)) = d108 pattern
  rw [s5976, s5963]
  rfl
theorem s5978 (pattern : Twelve) : d109 (change pattern 12 6) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d99 (change pattern 12 6)) = d109 pattern
  rw [s5921, s5954]
  rfl
theorem s5979 (pattern : Twelve) : d113 (change pattern 12 6) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 12 6) else d108 (change pattern 12 6)) = d113 pattern
  rw [s5978, s5977]
  rfl
theorem s5980 (pattern : Twelve) : d115 (change pattern 12 6) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 12 6) else d112 (change pattern 12 6)) = d115 pattern
  rw [s5979, s5956]
  rfl
theorem s5981 (pattern : Twelve) : d116 (change pattern 12 6) = d115 pattern := by
  change d115 (change pattern 12 6) = d115 pattern
  exact s5980 pattern
theorem s5982 (pattern : Twelve) : d778 (change pattern 12 6) = d778 pattern := by
  change (if pattern.i then d3 (change pattern 12 6) else d2 (change pattern 12 6)) = d778 pattern
  rw [s5914, s5912]
  rfl
theorem s5983 (pattern : Twelve) : d779 (change pattern 12 6) = d779 pattern := by
  change (if pattern.i then d3 (change pattern 12 6) else d23 (change pattern 12 6)) = d779 pattern
  rw [s5914, s5916]
  rfl
theorem s5984 (pattern : Twelve) : d782 (change pattern 12 6) = d782 pattern := by
  change (if pattern.h then d779 (change pattern 12 6) else d778 (change pattern 12 6)) = d782 pattern
  rw [s5983, s5982]
  rfl
theorem s5985 (pattern : Twelve) : d788 (change pattern 12 6) = d788 pattern := by
  change (if pattern.f then d782 (change pattern 12 6) else d2 (change pattern 12 6)) = d788 pattern
  rw [s5984, s5912]
  rfl
theorem s5986 (pattern : Twelve) : d16 (change pattern 12 6) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 6) else d2 (change pattern 12 6)) = d16 pattern
  rw [s5928, s5912]
  rfl
theorem s5987 (pattern : Twelve) : d25 (change pattern 12 6) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 6) else d16 (change pattern 12 6)) = d25 pattern
  rw [s5927, s5986]
  rfl
theorem s5988 (pattern : Twelve) : d42 (change pattern 12 6) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d25 (change pattern 12 6)) = d42 pattern
  rw [s5921, s5987]
  rfl
theorem s5989 (pattern : Twelve) : d61 (change pattern 12 6) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 12 6) else d41 (change pattern 12 6)) = d61 pattern
  rw [s5988, s5972]
  rfl
theorem s5990 (pattern : Twelve) : d789 (change pattern 12 6) = d789 pattern := by
  change (if pattern.f then d61 (change pattern 12 6) else d38 (change pattern 12 6)) = d789 pattern
  rw [s5989, s5960]
  rfl
theorem s5991 (pattern : Twelve) : d794 (change pattern 12 6) = d794 pattern := by
  change (if pattern.e then d789 (change pattern 12 6) else d788 (change pattern 12 6)) = d794 pattern
  rw [s5990, s5985]
  rfl
theorem s5992 (pattern : Twelve) : d783 (change pattern 12 6) = d783 pattern := by
  change (if pattern.h then d44 (change pattern 12 6) else d38 (change pattern 12 6)) = d783 pattern
  rw [s5939, s5960]
  rfl
theorem s5993 (pattern : Twelve) : d790 (change pattern 12 6) = d790 pattern := by
  change (if pattern.f then d69 (change pattern 12 6) else d783 (change pattern 12 6)) = d790 pattern
  rw [s5966, s5992]
  rfl
theorem s5994 (pattern : Twelve) : d795 (change pattern 12 6) = d795 pattern := by
  change (if pattern.e then d90 (change pattern 12 6) else d790 (change pattern 12 6)) = d795 pattern
  rw [s5975, s5993]
  rfl
theorem s5995 (pattern : Twelve) : d798 (change pattern 12 6) = d798 pattern := by
  change (if pattern.j then d795 (change pattern 12 6) else d794 (change pattern 12 6)) = d798 pattern
  rw [s5994, s5991]
  rfl
theorem s5996 (pattern : Twelve) : d799 (change pattern 12 6) = d799 pattern := by
  change (if pattern.j then d101 (change pattern 12 6) else d794 (change pattern 12 6)) = d799 pattern
  rw [s5976, s5991]
  rfl
theorem s5997 (pattern : Twelve) : d802 (change pattern 12 6) = d802 pattern := by
  change (if pattern.d then d799 (change pattern 12 6) else d798 (change pattern 12 6)) = d802 pattern
  rw [s5996, s5995]
  rfl
theorem s5998 (pattern : Twelve) : d780 (change pattern 12 6) = d780 pattern := by
  change (if pattern.i then d5 (change pattern 12 6) else d3 (change pattern 12 6)) = d780 pattern
  rw [s5926, s5914]
  rfl
theorem s5999 (pattern : Twelve) : d784 (change pattern 12 6) = d784 pattern := by
  change (if pattern.h then d780 (change pattern 12 6) else d38 (change pattern 12 6)) = d784 pattern
  rw [s5998, s5960]
  rfl
end NetHack.Sokoban21.Diagram
