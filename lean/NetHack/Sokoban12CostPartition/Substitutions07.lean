/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub840 (p : Pattern) : d54 (change p 134 (some 133)) = d54 p := by
  change (if p 193 then d4 (change p 134 (some 133)) else d2 (change p 134 (some 133))) = d54 p
  rw [sub839, sub836]
  rfl
theorem sub841 (p : Pattern) : d55 (change p 134 (some 133)) = d55 p := by
  change (if p 192 then d54 (change p 134 (some 133)) else d2 (change p 134 (some 133))) = d55 p
  rw [sub840, sub836]
  rfl
theorem sub842 (p : Pattern) : d56 (change p 134 (some 133)) = d56 p := by
  change (if p 186 then d55 (change p 134 (some 133)) else d7 (change p 134 (some 133))) = d56 p
  rw [sub841, sub838]
  rfl
theorem sub843 (p : Pattern) : d57 (change p 134 (some 133)) = d57 p := by
  change (if p 160 then d56 (change p 134 (some 133)) else d7 (change p 134 (some 133))) = d57 p
  rw [sub842, sub838]
  rfl
theorem sub844 (p : Pattern) : d68 (change p 134 (some 133)) = d68 p := by
  change (if p 158 then d55 (change p 134 (some 133)) else d57 (change p 134 (some 133))) = d68 p
  rw [sub841, sub843]
  rfl
theorem sub845 (p : Pattern) : d1 (change p 134 (some 133)) = d1 p := by
  rfl
theorem sub846 (p : Pattern) : d8 (change p 134 (some 133)) = d8 p := by
  change (if p 271 then d1 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d8 p
  rw [sub845, sub835]
  rfl
theorem sub847 (p : Pattern) : d3 (change p 134 (some 133)) = d3 p := by
  rfl
theorem sub848 (p : Pattern) : d9 (change p 134 (some 133)) = d9 p := by
  change (if p 271 then d3 (change p 134 (some 133)) else d2 (change p 134 (some 133))) = d9 p
  rw [sub847, sub836]
  rfl
theorem sub849 (p : Pattern) : d10 (change p 134 (some 133)) = d10 p := by
  change (if p 193 then d9 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d10 p
  rw [sub848, sub846]
  rfl
theorem sub850 (p : Pattern) : d11 (change p 134 (some 133)) = d11 p := by
  change (if p 192 then d10 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d11 p
  rw [sub849, sub846]
  rfl
theorem sub851 (p : Pattern) : d12 (change p 134 (some 133)) = d12 p := by
  change (if p 168 then d11 (change p 134 (some 133)) else d7 (change p 134 (some 133))) = d12 p
  rw [sub850, sub838]
  rfl
theorem sub852 (p : Pattern) : d5 (change p 134 (some 133)) = d5 p := by
  rfl
theorem sub853 (p : Pattern) : d58 (change p 134 (some 133)) = d58 p := by
  change (if p 271 then d5 (change p 134 (some 133)) else d4 (change p 134 (some 133))) = d58 p
  rw [sub852, sub839]
  rfl
theorem sub854 (p : Pattern) : d59 (change p 134 (some 133)) = d59 p := by
  change (if p 193 then d58 (change p 134 (some 133)) else d9 (change p 134 (some 133))) = d59 p
  rw [sub853, sub848]
  rfl
theorem sub855 (p : Pattern) : d60 (change p 134 (some 133)) = d60 p := by
  change (if p 192 then d59 (change p 134 (some 133)) else d9 (change p 134 (some 133))) = d60 p
  rw [sub854, sub848]
  rfl
theorem sub856 (p : Pattern) : d61 (change p 134 (some 133)) = d61 p := by
  change (if p 186 then d60 (change p 134 (some 133)) else d11 (change p 134 (some 133))) = d61 p
  rw [sub855, sub850]
  rfl
theorem sub857 (p : Pattern) : d62 (change p 134 (some 133)) = d62 p := by
  change (if p 168 then d61 (change p 134 (some 133)) else d56 (change p 134 (some 133))) = d62 p
  rw [sub856, sub842]
  rfl
theorem sub858 (p : Pattern) : d63 (change p 134 (some 133)) = d63 p := by
  change (if p 160 then d62 (change p 134 (some 133)) else d12 (change p 134 (some 133))) = d63 p
  rw [sub857, sub851]
  rfl
theorem sub859 (p : Pattern) : d65 (change p 134 (some 133)) = d65 p := by
  change (if p 168 then d60 (change p 134 (some 133)) else d55 (change p 134 (some 133))) = d65 p
  rw [sub855, sub841]
  rfl
theorem sub860 (p : Pattern) : d69 (change p 134 (some 133)) = d69 p := by
  change (if p 158 then d65 (change p 134 (some 133)) else d63 (change p 134 (some 133))) = d69 p
  rw [sub859, sub858]
  rfl
theorem sub861 (p : Pattern) : d70 (change p 134 (some 133)) = d70 p := by
  change (if p 141 then d69 (change p 134 (some 133)) else d68 (change p 134 (some 133))) = d70 p
  rw [sub860, sub844]
  rfl
theorem sub862 (p : Pattern) : d71 (change p 134 (some 133)) = d70 p := by
  change d70 (change p 134 (some 133)) = d70 p
  exact sub861 p
theorem sub863 (p : Pattern) : d72 (change p 134 (some 133)) = d70 p := by
  change d71 (change p 134 (some 133)) = d70 p
  exact sub862 p
theorem sub864 (p : Pattern) : d66 (change p 134 (some 133)) = d66 p := by
  change (if p 141 then d65 (change p 134 (some 133)) else d55 (change p 134 (some 133))) = d66 p
  rw [sub859, sub841]
  rfl
theorem sub865 (p : Pattern) : d73 (change p 134 (some 133)) = d66 p := by
  change d66 (change p 134 (some 133)) = d66 p
  exact sub864 p
theorem sub866 (p : Pattern) : d74 (change p 134 (some 133)) = d852 p := by
  change (if p 132 then d73 (change p 134 (some 133)) else d72 (change p 134 (some 133))) = d852 p
  rw [sub865, sub863]
  rfl
theorem sub867 (p : Pattern) : d0 (change p 10000 (some 192)) = d0 p := by
  rfl
theorem sub868 (p : Pattern) : d2 (change p 10000 (some 192)) = d2 p := by
  rfl
theorem sub869 (p : Pattern) : d6 (change p 10000 (some 192)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 192)) else d0 (change p 10000 (some 192))) = d6 p
  rw [sub868, sub867]
  rfl
theorem sub870 (p : Pattern) : d7 (change p 10000 (some 192)) = d6 p := by
  change d6 (change p 10000 (some 192)) = d6 p
  exact sub869 p
theorem sub871 (p : Pattern) : d4 (change p 10000 (some 192)) = d4 p := by
  rfl
theorem sub872 (p : Pattern) : d54 (change p 10000 (some 192)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 192)) else d2 (change p 10000 (some 192))) = d54 p
  rw [sub871, sub868]
  rfl
theorem sub873 (p : Pattern) : d55 (change p 10000 (some 192)) = d54 p := by
  change d54 (change p 10000 (some 192)) = d54 p
  exact sub872 p
theorem sub874 (p : Pattern) : d56 (change p 10000 (some 192)) = d855 p := by
  change (if p 186 then d55 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d855 p
  rw [sub873, sub870]
  rfl
theorem sub875 (p : Pattern) : d57 (change p 10000 (some 192)) = d856 p := by
  change (if p 160 then d56 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d856 p
  rw [sub874, sub870]
  rfl
theorem sub876 (p : Pattern) : d1 (change p 10000 (some 192)) = d1 p := by
  rfl
theorem sub877 (p : Pattern) : d8 (change p 10000 (some 192)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 192)) else d0 (change p 10000 (some 192))) = d8 p
  rw [sub876, sub867]
  rfl
theorem sub878 (p : Pattern) : d3 (change p 10000 (some 192)) = d3 p := by
  rfl
theorem sub879 (p : Pattern) : d9 (change p 10000 (some 192)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 192)) else d2 (change p 10000 (some 192))) = d9 p
  rw [sub878, sub868]
  rfl
theorem sub880 (p : Pattern) : d10 (change p 10000 (some 192)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 192)) else d8 (change p 10000 (some 192))) = d10 p
  rw [sub879, sub877]
  rfl
theorem sub881 (p : Pattern) : d11 (change p 10000 (some 192)) = d10 p := by
  change d10 (change p 10000 (some 192)) = d10 p
  exact sub880 p
theorem sub882 (p : Pattern) : d12 (change p 10000 (some 192)) = d857 p := by
  change (if p 168 then d11 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d857 p
  rw [sub881, sub870]
  rfl
theorem sub883 (p : Pattern) : d5 (change p 10000 (some 192)) = d5 p := by
  rfl
theorem sub884 (p : Pattern) : d58 (change p 10000 (some 192)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 192)) else d4 (change p 10000 (some 192))) = d58 p
  rw [sub883, sub871]
  rfl
theorem sub885 (p : Pattern) : d59 (change p 10000 (some 192)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 192)) else d9 (change p 10000 (some 192))) = d59 p
  rw [sub884, sub879]
  rfl
theorem sub886 (p : Pattern) : d60 (change p 10000 (some 192)) = d59 p := by
  change d59 (change p 10000 (some 192)) = d59 p
  exact sub885 p
theorem sub887 (p : Pattern) : d61 (change p 10000 (some 192)) = d858 p := by
  change (if p 186 then d60 (change p 10000 (some 192)) else d11 (change p 10000 (some 192))) = d858 p
  rw [sub886, sub881]
  rfl
theorem sub888 (p : Pattern) : d62 (change p 10000 (some 192)) = d859 p := by
  change (if p 168 then d61 (change p 10000 (some 192)) else d56 (change p 10000 (some 192))) = d859 p
  rw [sub887, sub874]
  rfl
theorem sub889 (p : Pattern) : d63 (change p 10000 (some 192)) = d860 p := by
  change (if p 160 then d62 (change p 10000 (some 192)) else d12 (change p 10000 (some 192))) = d860 p
  rw [sub888, sub882]
  rfl
theorem sub890 (p : Pattern) : d64 (change p 10000 (some 192)) = d861 p := by
  change (if p 141 then d63 (change p 10000 (some 192)) else d57 (change p 10000 (some 192))) = d861 p
  rw [sub889, sub875]
  rfl
theorem sub891 (p : Pattern) : d106 (change p 10000 (some 192)) = d862 p := by
  change (if p 160 then d55 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d862 p
  rw [sub873, sub870]
  rfl
theorem sub892 (p : Pattern) : d119 (change p 10000 (some 192)) = d863 p := by
  change (if p 187 then d55 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d863 p
  rw [sub873, sub870]
  rfl
theorem sub893 (p : Pattern) : d120 (change p 10000 (some 192)) = d864 p := by
  change (if p 186 then d119 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d864 p
  rw [sub892, sub870]
  rfl
theorem sub894 (p : Pattern) : d121 (change p 10000 (some 192)) = d865 p := by
  change (if p 160 then d55 (change p 10000 (some 192)) else d120 (change p 10000 (some 192))) = d865 p
  rw [sub873, sub893]
  rfl
theorem sub895 (p : Pattern) : d122 (change p 10000 (some 192)) = d866 p := by
  change (if p 159 then d121 (change p 10000 (some 192)) else d106 (change p 10000 (some 192))) = d866 p
  rw [sub894, sub891]
  rfl
theorem sub896 (p : Pattern) : d179 (change p 10000 (some 192)) = d867 p := by
  change (if p 158 then d122 (change p 10000 (some 192)) else d106 (change p 10000 (some 192))) = d867 p
  rw [sub895, sub891]
  rfl
theorem sub897 (p : Pattern) : d65 (change p 10000 (some 192)) = d868 p := by
  change (if p 168 then d60 (change p 10000 (some 192)) else d55 (change p 10000 (some 192))) = d868 p
  rw [sub886, sub873]
  rfl
theorem sub898 (p : Pattern) : d109 (change p 10000 (some 192)) = d869 p := by
  change (if p 160 then d65 (change p 10000 (some 192)) else d12 (change p 10000 (some 192))) = d869 p
  rw [sub897, sub882]
  rfl
theorem sub899 (p : Pattern) : d125 (change p 10000 (some 192)) = d870 p := by
  change (if p 187 then d60 (change p 10000 (some 192)) else d11 (change p 10000 (some 192))) = d870 p
  rw [sub886, sub881]
  rfl
theorem sub900 (p : Pattern) : d126 (change p 10000 (some 192)) = d871 p := by
  change (if p 186 then d125 (change p 10000 (some 192)) else d11 (change p 10000 (some 192))) = d871 p
  rw [sub899, sub881]
  rfl
theorem sub901 (p : Pattern) : d127 (change p 10000 (some 192)) = d872 p := by
  change (if p 168 then d126 (change p 10000 (some 192)) else d120 (change p 10000 (some 192))) = d872 p
  rw [sub900, sub893]
  rfl
theorem sub902 (p : Pattern) : d128 (change p 10000 (some 192)) = d873 p := by
  change (if p 160 then d65 (change p 10000 (some 192)) else d127 (change p 10000 (some 192))) = d873 p
  rw [sub897, sub901]
  rfl
theorem sub903 (p : Pattern) : d129 (change p 10000 (some 192)) = d874 p := by
  change (if p 159 then d128 (change p 10000 (some 192)) else d109 (change p 10000 (some 192))) = d874 p
  rw [sub902, sub898]
  rfl
theorem sub904 (p : Pattern) : d237 (change p 10000 (some 192)) = d875 p := by
  change (if p 158 then d129 (change p 10000 (some 192)) else d109 (change p 10000 (some 192))) = d875 p
  rw [sub903, sub898]
  rfl
theorem sub905 (p : Pattern) : d238 (change p 10000 (some 192)) = d876 p := by
  change (if p 141 then d237 (change p 10000 (some 192)) else d179 (change p 10000 (some 192))) = d876 p
  rw [sub904, sub896]
  rfl
theorem sub906 (p : Pattern) : d239 (change p 10000 (some 192)) = d877 p := by
  change (if p 134 then d238 (change p 10000 (some 192)) else d64 (change p 10000 (some 192))) = d877 p
  rw [sub905, sub890]
  rfl
theorem sub907 (p : Pattern) : d68 (change p 10000 (some 192)) = d878 p := by
  change (if p 158 then d55 (change p 10000 (some 192)) else d57 (change p 10000 (some 192))) = d878 p
  rw [sub873, sub875]
  rfl
theorem sub908 (p : Pattern) : d69 (change p 10000 (some 192)) = d879 p := by
  change (if p 158 then d65 (change p 10000 (some 192)) else d63 (change p 10000 (some 192))) = d879 p
  rw [sub897, sub889]
  rfl
theorem sub909 (p : Pattern) : d70 (change p 10000 (some 192)) = d880 p := by
  change (if p 141 then d69 (change p 10000 (some 192)) else d68 (change p 10000 (some 192))) = d880 p
  rw [sub908, sub907]
  rfl
theorem sub910 (p : Pattern) : d181 (change p 10000 (some 192)) = d881 p := by
  change (if p 158 then d55 (change p 10000 (some 192)) else d122 (change p 10000 (some 192))) = d881 p
  rw [sub873, sub895]
  rfl
theorem sub911 (p : Pattern) : d240 (change p 10000 (some 192)) = d882 p := by
  change (if p 158 then d65 (change p 10000 (some 192)) else d129 (change p 10000 (some 192))) = d882 p
  rw [sub897, sub903]
  rfl
theorem sub912 (p : Pattern) : d241 (change p 10000 (some 192)) = d883 p := by
  change (if p 141 then d240 (change p 10000 (some 192)) else d181 (change p 10000 (some 192))) = d883 p
  rw [sub911, sub910]
  rfl
theorem sub913 (p : Pattern) : d242 (change p 10000 (some 192)) = d884 p := by
  change (if p 134 then d241 (change p 10000 (some 192)) else d70 (change p 10000 (some 192))) = d884 p
  rw [sub912, sub909]
  rfl
theorem sub914 (p : Pattern) : d243 (change p 10000 (some 192)) = d885 p := by
  change (if p 133 then d242 (change p 10000 (some 192)) else d239 (change p 10000 (some 192))) = d885 p
  rw [sub913, sub906]
  rfl
theorem sub915 (p : Pattern) : d66 (change p 10000 (some 192)) = d886 p := by
  change (if p 141 then d65 (change p 10000 (some 192)) else d55 (change p 10000 (some 192))) = d886 p
  rw [sub897, sub873]
  rfl
theorem sub916 (p : Pattern) : d244 (change p 10000 (some 192)) = d887 p := by
  change (if p 133 then d66 (change p 10000 (some 192)) else d242 (change p 10000 (some 192))) = d887 p
  rw [sub915, sub913]
  rfl
theorem sub917 (p : Pattern) : d245 (change p 10000 (some 192)) = d888 p := by
  change (if p 132 then d244 (change p 10000 (some 192)) else d243 (change p 10000 (some 192))) = d888 p
  rw [sub916, sub914]
  rfl
theorem sub918 (p : Pattern) : d137 (change p 10000 (some 192)) = d889 p := by
  change (if p 186 then d55 (change p 10000 (some 192)) else d119 (change p 10000 (some 192))) = d889 p
  rw [sub873, sub892]
  rfl
theorem sub919 (p : Pattern) : d139 (change p 10000 (some 192)) = d890 p := by
  change (if p 160 then d137 (change p 10000 (some 192)) else d120 (change p 10000 (some 192))) = d890 p
  rw [sub918, sub893]
  rfl
theorem sub920 (p : Pattern) : d153 (change p 10000 (some 192)) = d891 p := by
  change (if p 159 then d139 (change p 10000 (some 192)) else d57 (change p 10000 (some 192))) = d891 p
  rw [sub919, sub875]
  rfl
theorem sub921 (p : Pattern) : d186 (change p 10000 (some 192)) = d892 p := by
  change (if p 158 then d153 (change p 10000 (some 192)) else d57 (change p 10000 (some 192))) = d892 p
  rw [sub920, sub875]
  rfl
theorem sub922 (p : Pattern) : d143 (change p 10000 (some 192)) = d893 p := by
  change (if p 186 then d60 (change p 10000 (some 192)) else d125 (change p 10000 (some 192))) = d893 p
  rw [sub886, sub899]
  rfl
theorem sub923 (p : Pattern) : d144 (change p 10000 (some 192)) = d894 p := by
  change (if p 168 then d143 (change p 10000 (some 192)) else d137 (change p 10000 (some 192))) = d894 p
  rw [sub922, sub918]
  rfl
theorem sub924 (p : Pattern) : d146 (change p 10000 (some 192)) = d895 p := by
  change (if p 160 then d144 (change p 10000 (some 192)) else d127 (change p 10000 (some 192))) = d895 p
  rw [sub923, sub901]
  rfl
theorem sub925 (p : Pattern) : d155 (change p 10000 (some 192)) = d896 p := by
  change (if p 159 then d146 (change p 10000 (some 192)) else d63 (change p 10000 (some 192))) = d896 p
  rw [sub924, sub889]
  rfl
theorem sub926 (p : Pattern) : d246 (change p 10000 (some 192)) = d897 p := by
  change (if p 158 then d155 (change p 10000 (some 192)) else d63 (change p 10000 (some 192))) = d897 p
  rw [sub925, sub889]
  rfl
theorem sub927 (p : Pattern) : d247 (change p 10000 (some 192)) = d898 p := by
  change (if p 141 then d246 (change p 10000 (some 192)) else d186 (change p 10000 (some 192))) = d898 p
  rw [sub926, sub921]
  rfl
theorem sub928 (p : Pattern) : d248 (change p 10000 (some 192)) = d899 p := by
  change (if p 134 then d66 (change p 10000 (some 192)) else d247 (change p 10000 (some 192))) = d899 p
  rw [sub915, sub927]
  rfl
theorem sub929 (p : Pattern) : d138 (change p 10000 (some 192)) = d900 p := by
  change (if p 160 then d137 (change p 10000 (some 192)) else d7 (change p 10000 (some 192))) = d900 p
  rw [sub918, sub870]
  rfl
theorem sub930 (p : Pattern) : d140 (change p 10000 (some 192)) = d901 p := by
  change (if p 159 then d139 (change p 10000 (some 192)) else d138 (change p 10000 (some 192))) = d901 p
  rw [sub919, sub929]
  rfl
theorem sub931 (p : Pattern) : d188 (change p 10000 (some 192)) = d902 p := by
  change (if p 158 then d55 (change p 10000 (some 192)) else d140 (change p 10000 (some 192))) = d902 p
  rw [sub873, sub930]
  rfl
theorem sub932 (p : Pattern) : d145 (change p 10000 (some 192)) = d903 p := by
  change (if p 160 then d144 (change p 10000 (some 192)) else d12 (change p 10000 (some 192))) = d903 p
  rw [sub923, sub882]
  rfl
theorem sub933 (p : Pattern) : d147 (change p 10000 (some 192)) = d904 p := by
  change (if p 159 then d146 (change p 10000 (some 192)) else d145 (change p 10000 (some 192))) = d904 p
  rw [sub924, sub932]
  rfl
theorem sub934 (p : Pattern) : d249 (change p 10000 (some 192)) = d905 p := by
  change (if p 158 then d65 (change p 10000 (some 192)) else d147 (change p 10000 (some 192))) = d905 p
  rw [sub897, sub933]
  rfl
theorem sub935 (p : Pattern) : d250 (change p 10000 (some 192)) = d906 p := by
  change (if p 141 then d249 (change p 10000 (some 192)) else d188 (change p 10000 (some 192))) = d906 p
  rw [sub934, sub931]
  rfl
theorem sub936 (p : Pattern) : d251 (change p 10000 (some 192)) = d907 p := by
  change (if p 134 then d66 (change p 10000 (some 192)) else d250 (change p 10000 (some 192))) = d907 p
  rw [sub915, sub935]
  rfl
theorem sub937 (p : Pattern) : d252 (change p 10000 (some 192)) = d908 p := by
  change (if p 133 then d251 (change p 10000 (some 192)) else d248 (change p 10000 (some 192))) = d908 p
  rw [sub936, sub928]
  rfl
theorem sub938 (p : Pattern) : d191 (change p 10000 (some 192)) = d909 p := by
  change (if p 158 then d55 (change p 10000 (some 192)) else d153 (change p 10000 (some 192))) = d909 p
  rw [sub873, sub920]
  rfl
theorem sub939 (p : Pattern) : d253 (change p 10000 (some 192)) = d910 p := by
  change (if p 158 then d65 (change p 10000 (some 192)) else d155 (change p 10000 (some 192))) = d910 p
  rw [sub897, sub925]
  rfl
theorem sub940 (p : Pattern) : d254 (change p 10000 (some 192)) = d911 p := by
  change (if p 141 then d253 (change p 10000 (some 192)) else d191 (change p 10000 (some 192))) = d911 p
  rw [sub939, sub938]
  rfl
theorem sub941 (p : Pattern) : d255 (change p 10000 (some 192)) = d912 p := by
  change (if p 134 then d66 (change p 10000 (some 192)) else d254 (change p 10000 (some 192))) = d912 p
  rw [sub915, sub940]
  rfl
theorem sub942 (p : Pattern) : d256 (change p 10000 (some 192)) = d913 p := by
  change (if p 133 then d66 (change p 10000 (some 192)) else d255 (change p 10000 (some 192))) = d913 p
  rw [sub915, sub941]
  rfl
theorem sub943 (p : Pattern) : d257 (change p 10000 (some 192)) = d914 p := by
  change (if p 132 then d256 (change p 10000 (some 192)) else d252 (change p 10000 (some 192))) = d914 p
  rw [sub942, sub937]
  rfl
theorem sub944 (p : Pattern) : d258 (change p 10000 (some 192)) = d915 p := by
  change (if p 108 then d257 (change p 10000 (some 192)) else d245 (change p 10000 (some 192))) = d915 p
  rw [sub943, sub917]
  rfl
theorem sub945 (p : Pattern) : d0 (change p 10000 (some 193)) = d0 p := by
  rfl
theorem sub946 (p : Pattern) : d2 (change p 10000 (some 193)) = d2 p := by
  rfl
theorem sub947 (p : Pattern) : d6 (change p 10000 (some 193)) = d2 p := by
  change d2 (change p 10000 (some 193)) = d2 p
  exact sub946 p
theorem sub948 (p : Pattern) : d7 (change p 10000 (some 193)) = d919 p := by
  change (if p 192 then d6 (change p 10000 (some 193)) else d0 (change p 10000 (some 193))) = d919 p
  rw [sub947, sub945]
  rfl
theorem sub949 (p : Pattern) : d4 (change p 10000 (some 193)) = d4 p := by
  rfl
theorem sub950 (p : Pattern) : d54 (change p 10000 (some 193)) = d4 p := by
  change d4 (change p 10000 (some 193)) = d4 p
  exact sub949 p
theorem sub951 (p : Pattern) : d55 (change p 10000 (some 193)) = d920 p := by
  change (if p 192 then d54 (change p 10000 (some 193)) else d2 (change p 10000 (some 193))) = d920 p
  rw [sub950, sub946]
  rfl
theorem sub952 (p : Pattern) : d56 (change p 10000 (some 193)) = d921 p := by
  change (if p 186 then d55 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d921 p
  rw [sub951, sub948]
  rfl
theorem sub953 (p : Pattern) : d57 (change p 10000 (some 193)) = d922 p := by
  change (if p 160 then d56 (change p 10000 (some 193)) else d7 (change p 10000 (some 193))) = d922 p
  rw [sub952, sub948]
  rfl
theorem sub954 (p : Pattern) : d1 (change p 10000 (some 193)) = d1 p := by
  rfl
theorem sub955 (p : Pattern) : d8 (change p 10000 (some 193)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 193)) else d0 (change p 10000 (some 193))) = d8 p
  rw [sub954, sub945]
  rfl
theorem sub956 (p : Pattern) : d3 (change p 10000 (some 193)) = d3 p := by
  rfl
theorem sub957 (p : Pattern) : d9 (change p 10000 (some 193)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 193)) else d2 (change p 10000 (some 193))) = d9 p
  rw [sub956, sub946]
  rfl
theorem sub958 (p : Pattern) : d10 (change p 10000 (some 193)) = d9 p := by
  change d9 (change p 10000 (some 193)) = d9 p
  exact sub957 p
theorem sub959 (p : Pattern) : d11 (change p 10000 (some 193)) = d923 p := by
  change (if p 192 then d10 (change p 10000 (some 193)) else d8 (change p 10000 (some 193))) = d923 p
  rw [sub958, sub955]
  rfl
end NetHack.Sokoban12CostPartition
