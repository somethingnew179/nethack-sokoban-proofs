/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub840 (p : Pattern) : d19 (change p 49 none) = d19 p := by
  change (if p 204 then d12 (change p 49 none) else d18 (change p 49 none)) = d19 p
  rw [sub832, sub839]
  rfl
theorem sub841 (p : Pattern) : d20 (change p 49 none) = d20 p := by
  change (if p 182 then d19 (change p 49 none) else d18 (change p 49 none)) = d20 p
  rw [sub840, sub839]
  rfl
theorem sub842 (p : Pattern) : d21 (change p 49 none) = d21 p := by
  change (if p 163 then d20 (change p 49 none) else d16 (change p 49 none)) = d21 p
  rw [sub841, sub836]
  rfl
theorem sub843 (p : Pattern) : d22 (change p 49 none) = d22 p := by
  change (if p 162 then d21 (change p 49 none) else d16 (change p 49 none)) = d22 p
  rw [sub842, sub836]
  rfl
theorem sub844 (p : Pattern) : d9 (change p 49 none) = d9 p := by
  rfl
theorem sub845 (p : Pattern) : d23 (change p 49 none) = d23 p := by
  change (if p 247 then d12 (change p 49 none) else d9 (change p 49 none)) = d23 p
  rw [sub832, sub844]
  rfl
theorem sub846 (p : Pattern) : d24 (change p 49 none) = d24 p := by
  change (if p 246 then d23 (change p 49 none) else d9 (change p 49 none)) = d24 p
  rw [sub845, sub844]
  rfl
theorem sub847 (p : Pattern) : d25 (change p 49 none) = d25 p := by
  change (if p 204 then d12 (change p 49 none) else d24 (change p 49 none)) = d25 p
  rw [sub832, sub846]
  rfl
theorem sub848 (p : Pattern) : d26 (change p 49 none) = d26 p := by
  change (if p 182 then d25 (change p 49 none) else d24 (change p 49 none)) = d26 p
  rw [sub847, sub846]
  rfl
theorem sub849 (p : Pattern) : d27 (change p 49 none) = d27 p := by
  change (if p 163 then d12 (change p 49 none) else d26 (change p 49 none)) = d27 p
  rw [sub832, sub848]
  rfl
theorem sub850 (p : Pattern) : d28 (change p 49 none) = d28 p := by
  change (if p 162 then d27 (change p 49 none) else d21 (change p 49 none)) = d28 p
  rw [sub849, sub842]
  rfl
theorem sub851 (p : Pattern) : d29 (change p 49 none) = d29 p := by
  change (if p 161 then d28 (change p 49 none) else d22 (change p 49 none)) = d29 p
  rw [sub850, sub843]
  rfl
theorem sub852 (p : Pattern) : d2 (change p 49 none) = d2 p := by
  rfl
theorem sub853 (p : Pattern) : d30 (change p 49 none) = d30 p := by
  change (if p 247 then d12 (change p 49 none) else d2 (change p 49 none)) = d30 p
  rw [sub832, sub852]
  rfl
theorem sub854 (p : Pattern) : d31 (change p 49 none) = d31 p := by
  change (if p 246 then d30 (change p 49 none) else d2 (change p 49 none)) = d31 p
  rw [sub853, sub852]
  rfl
theorem sub855 (p : Pattern) : d32 (change p 49 none) = d32 p := by
  change (if p 204 then d12 (change p 49 none) else d31 (change p 49 none)) = d32 p
  rw [sub832, sub854]
  rfl
theorem sub856 (p : Pattern) : d33 (change p 49 none) = d33 p := by
  change (if p 182 then d32 (change p 49 none) else d14 (change p 49 none)) = d33 p
  rw [sub855, sub834]
  rfl
theorem sub857 (p : Pattern) : d6 (change p 49 none) = d6 p := by
  rfl
theorem sub858 (p : Pattern) : d34 (change p 49 none) = d34 p := by
  change (if p 247 then d12 (change p 49 none) else d6 (change p 49 none)) = d34 p
  rw [sub832, sub857]
  rfl
theorem sub859 (p : Pattern) : d35 (change p 49 none) = d35 p := by
  change (if p 246 then d34 (change p 49 none) else d6 (change p 49 none)) = d35 p
  rw [sub858, sub857]
  rfl
theorem sub860 (p : Pattern) : d36 (change p 49 none) = d36 p := by
  change (if p 204 then d12 (change p 49 none) else d35 (change p 49 none)) = d36 p
  rw [sub832, sub859]
  rfl
theorem sub861 (p : Pattern) : d37 (change p 49 none) = d37 p := by
  change (if p 182 then d36 (change p 49 none) else d14 (change p 49 none)) = d37 p
  rw [sub860, sub834]
  rfl
theorem sub862 (p : Pattern) : d38 (change p 49 none) = d38 p := by
  change (if p 163 then d37 (change p 49 none) else d33 (change p 49 none)) = d38 p
  rw [sub861, sub856]
  rfl
theorem sub863 (p : Pattern) : d11 (change p 49 none) = d11 p := by
  rfl
theorem sub864 (p : Pattern) : d39 (change p 49 none) = d39 p := by
  change (if p 247 then d12 (change p 49 none) else d11 (change p 49 none)) = d39 p
  rw [sub832, sub863]
  rfl
theorem sub865 (p : Pattern) : d40 (change p 49 none) = d40 p := by
  change (if p 246 then d39 (change p 49 none) else d11 (change p 49 none)) = d40 p
  rw [sub864, sub863]
  rfl
theorem sub866 (p : Pattern) : d41 (change p 49 none) = d41 p := by
  change (if p 204 then d12 (change p 49 none) else d40 (change p 49 none)) = d41 p
  rw [sub832, sub865]
  rfl
theorem sub867 (p : Pattern) : d42 (change p 49 none) = d42 p := by
  change (if p 182 then d41 (change p 49 none) else d14 (change p 49 none)) = d42 p
  rw [sub866, sub834]
  rfl
theorem sub868 (p : Pattern) : d43 (change p 49 none) = d43 p := by
  change (if p 182 then d12 (change p 49 none) else d18 (change p 49 none)) = d43 p
  rw [sub832, sub839]
  rfl
theorem sub869 (p : Pattern) : d44 (change p 49 none) = d44 p := by
  change (if p 163 then d43 (change p 49 none) else d42 (change p 49 none)) = d44 p
  rw [sub868, sub867]
  rfl
theorem sub870 (p : Pattern) : d45 (change p 49 none) = d45 p := by
  change (if p 162 then d44 (change p 49 none) else d38 (change p 49 none)) = d45 p
  rw [sub869, sub862]
  rfl
theorem sub871 (p : Pattern) : d46 (change p 49 none) = d46 p := by
  change (if p 182 then d12 (change p 49 none) else d14 (change p 49 none)) = d46 p
  rw [sub832, sub834]
  rfl
theorem sub872 (p : Pattern) : d47 (change p 49 none) = d47 p := by
  change (if p 163 then d43 (change p 49 none) else d46 (change p 49 none)) = d47 p
  rw [sub868, sub871]
  rfl
theorem sub873 (p : Pattern) : d48 (change p 49 none) = d48 p := by
  change (if p 182 then d12 (change p 49 none) else d24 (change p 49 none)) = d48 p
  rw [sub832, sub846]
  rfl
theorem sub874 (p : Pattern) : d49 (change p 49 none) = d49 p := by
  change (if p 163 then d12 (change p 49 none) else d48 (change p 49 none)) = d49 p
  rw [sub832, sub873]
  rfl
theorem sub875 (p : Pattern) : d50 (change p 49 none) = d50 p := by
  change (if p 162 then d49 (change p 49 none) else d47 (change p 49 none)) = d50 p
  rw [sub874, sub872]
  rfl
theorem sub876 (p : Pattern) : d51 (change p 49 none) = d51 p := by
  change (if p 161 then d50 (change p 49 none) else d45 (change p 49 none)) = d51 p
  rw [sub875, sub870]
  rfl
theorem sub877 (p : Pattern) : d52 (change p 49 none) = d52 p := by
  change (if p 160 then d51 (change p 49 none) else d29 (change p 49 none)) = d52 p
  rw [sub876, sub851]
  rfl
theorem sub878 (p : Pattern) : d53 (change p 49 none) = d53 p := by
  change (if p 182 then d32 (change p 49 none) else d31 (change p 49 none)) = d53 p
  rw [sub855, sub854]
  rfl
theorem sub879 (p : Pattern) : d54 (change p 49 none) = d54 p := by
  change (if p 163 then d53 (change p 49 none) else d16 (change p 49 none)) = d54 p
  rw [sub878, sub836]
  rfl
theorem sub880 (p : Pattern) : d55 (change p 49 none) = d55 p := by
  change (if p 163 then d26 (change p 49 none) else d20 (change p 49 none)) = d55 p
  rw [sub848, sub841]
  rfl
theorem sub881 (p : Pattern) : d56 (change p 49 none) = d56 p := by
  change (if p 162 then d55 (change p 49 none) else d54 (change p 49 none)) = d56 p
  rw [sub880, sub879]
  rfl
theorem sub882 (p : Pattern) : d10 (change p 49 none) = d10 p := by
  rfl
theorem sub883 (p : Pattern) : d57 (change p 49 none) = d57 p := by
  change (if p 247 then d12 (change p 49 none) else d10 (change p 49 none)) = d57 p
  rw [sub832, sub882]
  rfl
theorem sub884 (p : Pattern) : d58 (change p 49 none) = d58 p := by
  change (if p 246 then d57 (change p 49 none) else d10 (change p 49 none)) = d58 p
  rw [sub883, sub882]
  rfl
theorem sub885 (p : Pattern) : d59 (change p 49 none) = d59 p := by
  change (if p 204 then d12 (change p 49 none) else d58 (change p 49 none)) = d59 p
  rw [sub832, sub884]
  rfl
theorem sub886 (p : Pattern) : d60 (change p 49 none) = d60 p := by
  change (if p 182 then d59 (change p 49 none) else d58 (change p 49 none)) = d60 p
  rw [sub885, sub884]
  rfl
theorem sub887 (p : Pattern) : d61 (change p 49 none) = d61 p := by
  change (if p 163 then d60 (change p 49 none) else d20 (change p 49 none)) = d61 p
  rw [sub886, sub841]
  rfl
theorem sub888 (p : Pattern) : d62 (change p 49 none) = d62 p := by
  change (if p 182 then d41 (change p 49 none) else d40 (change p 49 none)) = d62 p
  rw [sub866, sub865]
  rfl
theorem sub889 (p : Pattern) : d63 (change p 49 none) = d63 p := by
  change (if p 163 then d12 (change p 49 none) else d62 (change p 49 none)) = d63 p
  rw [sub832, sub888]
  rfl
theorem sub890 (p : Pattern) : d64 (change p 49 none) = d64 p := by
  change (if p 162 then d63 (change p 49 none) else d61 (change p 49 none)) = d64 p
  rw [sub889, sub887]
  rfl
theorem sub891 (p : Pattern) : d65 (change p 49 none) = d65 p := by
  change (if p 161 then d64 (change p 49 none) else d56 (change p 49 none)) = d65 p
  rw [sub890, sub881]
  rfl
theorem sub892 (p : Pattern) : d66 (change p 49 none) = d66 p := by
  change (if p 182 then d12 (change p 49 none) else d31 (change p 49 none)) = d66 p
  rw [sub832, sub854]
  rfl
theorem sub893 (p : Pattern) : d67 (change p 49 none) = d67 p := by
  change (if p 163 then d66 (change p 49 none) else d37 (change p 49 none)) = d67 p
  rw [sub892, sub861]
  rfl
theorem sub894 (p : Pattern) : d68 (change p 49 none) = d68 p := by
  change (if p 163 then d48 (change p 49 none) else d43 (change p 49 none)) = d68 p
  rw [sub873, sub868]
  rfl
theorem sub895 (p : Pattern) : d69 (change p 49 none) = d69 p := by
  change (if p 162 then d68 (change p 49 none) else d67 (change p 49 none)) = d69 p
  rw [sub894, sub893]
  rfl
theorem sub896 (p : Pattern) : d70 (change p 49 none) = d70 p := by
  change (if p 182 then d12 (change p 49 none) else d58 (change p 49 none)) = d70 p
  rw [sub832, sub884]
  rfl
theorem sub897 (p : Pattern) : d71 (change p 49 none) = d71 p := by
  change (if p 163 then d70 (change p 49 none) else d43 (change p 49 none)) = d71 p
  rw [sub896, sub868]
  rfl
theorem sub898 (p : Pattern) : d72 (change p 49 none) = d72 p := by
  change (if p 182 then d12 (change p 49 none) else d40 (change p 49 none)) = d72 p
  rw [sub832, sub865]
  rfl
theorem sub899 (p : Pattern) : d73 (change p 49 none) = d73 p := by
  change (if p 163 then d12 (change p 49 none) else d72 (change p 49 none)) = d73 p
  rw [sub832, sub898]
  rfl
theorem sub900 (p : Pattern) : d74 (change p 49 none) = d74 p := by
  change (if p 162 then d73 (change p 49 none) else d71 (change p 49 none)) = d74 p
  rw [sub899, sub897]
  rfl
theorem sub901 (p : Pattern) : d75 (change p 49 none) = d75 p := by
  change (if p 161 then d74 (change p 49 none) else d69 (change p 49 none)) = d75 p
  rw [sub900, sub895]
  rfl
theorem sub902 (p : Pattern) : d76 (change p 49 none) = d76 p := by
  change (if p 160 then d75 (change p 49 none) else d65 (change p 49 none)) = d76 p
  rw [sub901, sub891]
  rfl
theorem sub903 (p : Pattern) : d77 (change p 49 none) = d77 p := by
  change (if p 141 then d76 (change p 49 none) else d52 (change p 49 none)) = d77 p
  rw [sub902, sub877]
  rfl
theorem sub904 (p : Pattern) : d78 (change p 49 none) = d78 p := by
  change (if p 182 then d36 (change p 49 none) else d35 (change p 49 none)) = d78 p
  rw [sub860, sub859]
  rfl
theorem sub905 (p : Pattern) : d79 (change p 49 none) = d79 p := by
  change (if p 163 then d78 (change p 49 none) else d53 (change p 49 none)) = d79 p
  rw [sub904, sub878]
  rfl
theorem sub906 (p : Pattern) : d80 (change p 49 none) = d80 p := by
  change (if p 162 then d63 (change p 49 none) else d79 (change p 49 none)) = d80 p
  rw [sub889, sub905]
  rfl
theorem sub907 (p : Pattern) : d81 (change p 49 none) = d81 p := by
  change (if p 161 then d12 (change p 49 none) else d80 (change p 49 none)) = d81 p
  rw [sub832, sub906]
  rfl
theorem sub908 (p : Pattern) : d82 (change p 49 none) = d82 p := by
  change (if p 160 then d81 (change p 49 none) else d29 (change p 49 none)) = d82 p
  rw [sub907, sub851]
  rfl
theorem sub909 (p : Pattern) : d83 (change p 49 none) = d83 p := by
  change (if p 163 then d12 (change p 49 none) else d78 (change p 49 none)) = d83 p
  rw [sub832, sub904]
  rfl
theorem sub910 (p : Pattern) : d84 (change p 49 none) = d84 p := by
  change (if p 162 then d12 (change p 49 none) else d83 (change p 49 none)) = d84 p
  rw [sub832, sub909]
  rfl
theorem sub911 (p : Pattern) : d85 (change p 49 none) = d85 p := by
  change (if p 161 then d12 (change p 49 none) else d84 (change p 49 none)) = d85 p
  rw [sub832, sub910]
  rfl
theorem sub912 (p : Pattern) : d86 (change p 49 none) = d86 p := by
  change (if p 160 then d85 (change p 49 none) else d65 (change p 49 none)) = d86 p
  rw [sub911, sub891]
  rfl
theorem sub913 (p : Pattern) : d87 (change p 49 none) = d87 p := by
  change (if p 141 then d86 (change p 49 none) else d82 (change p 49 none)) = d87 p
  rw [sub912, sub908]
  rfl
theorem sub914 (p : Pattern) : d88 (change p 49 none) = d88 p := by
  change (if p 138 then d87 (change p 49 none) else d77 (change p 49 none)) = d88 p
  rw [sub913, sub903]
  rfl
theorem sub915 (p : Pattern) : d89 (change p 49 none) = d89 p := by
  change (if p 163 then d62 (change p 49 none) else d26 (change p 49 none)) = d89 p
  rw [sub888, sub848]
  rfl
theorem sub916 (p : Pattern) : d90 (change p 49 none) = d90 p := by
  change (if p 162 then d63 (change p 49 none) else d89 (change p 49 none)) = d90 p
  rw [sub889, sub915]
  rfl
theorem sub917 (p : Pattern) : d91 (change p 49 none) = d91 p := by
  change (if p 162 then d12 (change p 49 none) else d63 (change p 49 none)) = d91 p
  rw [sub832, sub889]
  rfl
theorem sub918 (p : Pattern) : d92 (change p 49 none) = d92 p := by
  change (if p 161 then d91 (change p 49 none) else d90 (change p 49 none)) = d92 p
  rw [sub917, sub916]
  rfl
theorem sub919 (p : Pattern) : d93 (change p 49 none) = d93 p := by
  change (if p 161 then d12 (change p 49 none) else d91 (change p 49 none)) = d93 p
  rw [sub832, sub917]
  rfl
theorem sub920 (p : Pattern) : d94 (change p 49 none) = d94 p := by
  change (if p 160 then d93 (change p 49 none) else d92 (change p 49 none)) = d94 p
  rw [sub919, sub918]
  rfl
theorem sub921 (p : Pattern) : d95 (change p 49 none) = d95 p := by
  change (if p 160 then d12 (change p 49 none) else d93 (change p 49 none)) = d95 p
  rw [sub832, sub919]
  rfl
theorem sub922 (p : Pattern) : d96 (change p 49 none) = d96 p := by
  change (if p 141 then d95 (change p 49 none) else d94 (change p 49 none)) = d96 p
  rw [sub921, sub920]
  rfl
theorem sub923 (p : Pattern) : d97 (change p 49 none) = d97 p := by
  change (if p 138 then d96 (change p 49 none) else d87 (change p 49 none)) = d97 p
  rw [sub922, sub913]
  rfl
theorem sub924 (p : Pattern) : d98 (change p 49 none) = d98 p := by
  change (if p 116 then d97 (change p 49 none) else d88 (change p 49 none)) = d98 p
  rw [sub923, sub914]
  rfl
theorem sub925 (p : Pattern) : d99 (change p 49 none) = d99 p := by
  change (if p 138 then d12 (change p 49 none) else d87 (change p 49 none)) = d99 p
  rw [sub832, sub913]
  rfl
theorem sub926 (p : Pattern) : d100 (change p 49 none) = d100 p := by
  change (if p 116 then d99 (change p 49 none) else d88 (change p 49 none)) = d100 p
  rw [sub925, sub914]
  rfl
theorem sub927 (p : Pattern) : d101 (change p 49 none) = d101 p := by
  change (if p 115 then d100 (change p 49 none) else d98 (change p 49 none)) = d101 p
  rw [sub926, sub924]
  rfl
theorem sub928 (p : Pattern) : d482 (change p 49 none) = d101 p := by
  change d101 (change p 49 none) = d101 p
  exact sub927 p
theorem sub929 (p : Pattern) : d483 (change p 49 none) = d101 p := by
  change d101 (change p 49 none) = d101 p
  exact sub927 p
theorem sub930 (p : Pattern) : d484 (change p 49 none) = d101 p := by
  change (if p 48 then d483 (change p 49 none) else d482 (change p 49 none)) = d101 p
  rw [sub929, sub928]
  simp only [ite_self]
theorem sub931 (p : Pattern) : d0 (change p 71 none) = d0 p := by
  rfl
theorem sub932 (p : Pattern) : d12 (change p 71 none) = d12 p := by
  rfl
theorem sub933 (p : Pattern) : d13 (change p 71 none) = d13 p := by
  change (if p 247 then d12 (change p 71 none) else d0 (change p 71 none)) = d13 p
  rw [sub932, sub931]
  rfl
theorem sub934 (p : Pattern) : d14 (change p 71 none) = d14 p := by
  change (if p 246 then d13 (change p 71 none) else d0 (change p 71 none)) = d14 p
  rw [sub933, sub931]
  rfl
theorem sub935 (p : Pattern) : d15 (change p 71 none) = d15 p := by
  change (if p 204 then d12 (change p 71 none) else d14 (change p 71 none)) = d15 p
  rw [sub932, sub934]
  rfl
theorem sub936 (p : Pattern) : d16 (change p 71 none) = d16 p := by
  change (if p 182 then d15 (change p 71 none) else d14 (change p 71 none)) = d16 p
  rw [sub935, sub934]
  rfl
theorem sub937 (p : Pattern) : d4 (change p 71 none) = d4 p := by
  rfl
theorem sub938 (p : Pattern) : d17 (change p 71 none) = d17 p := by
  change (if p 247 then d12 (change p 71 none) else d4 (change p 71 none)) = d17 p
  rw [sub932, sub937]
  rfl
theorem sub939 (p : Pattern) : d18 (change p 71 none) = d18 p := by
  change (if p 246 then d17 (change p 71 none) else d4 (change p 71 none)) = d18 p
  rw [sub938, sub937]
  rfl
theorem sub940 (p : Pattern) : d19 (change p 71 none) = d19 p := by
  change (if p 204 then d12 (change p 71 none) else d18 (change p 71 none)) = d19 p
  rw [sub932, sub939]
  rfl
theorem sub941 (p : Pattern) : d20 (change p 71 none) = d20 p := by
  change (if p 182 then d19 (change p 71 none) else d18 (change p 71 none)) = d20 p
  rw [sub940, sub939]
  rfl
theorem sub942 (p : Pattern) : d21 (change p 71 none) = d21 p := by
  change (if p 163 then d20 (change p 71 none) else d16 (change p 71 none)) = d21 p
  rw [sub941, sub936]
  rfl
theorem sub943 (p : Pattern) : d22 (change p 71 none) = d22 p := by
  change (if p 162 then d21 (change p 71 none) else d16 (change p 71 none)) = d22 p
  rw [sub942, sub936]
  rfl
theorem sub944 (p : Pattern) : d9 (change p 71 none) = d9 p := by
  rfl
theorem sub945 (p : Pattern) : d23 (change p 71 none) = d23 p := by
  change (if p 247 then d12 (change p 71 none) else d9 (change p 71 none)) = d23 p
  rw [sub932, sub944]
  rfl
theorem sub946 (p : Pattern) : d24 (change p 71 none) = d24 p := by
  change (if p 246 then d23 (change p 71 none) else d9 (change p 71 none)) = d24 p
  rw [sub945, sub944]
  rfl
theorem sub947 (p : Pattern) : d25 (change p 71 none) = d25 p := by
  change (if p 204 then d12 (change p 71 none) else d24 (change p 71 none)) = d25 p
  rw [sub932, sub946]
  rfl
theorem sub948 (p : Pattern) : d26 (change p 71 none) = d26 p := by
  change (if p 182 then d25 (change p 71 none) else d24 (change p 71 none)) = d26 p
  rw [sub947, sub946]
  rfl
theorem sub949 (p : Pattern) : d27 (change p 71 none) = d27 p := by
  change (if p 163 then d12 (change p 71 none) else d26 (change p 71 none)) = d27 p
  rw [sub932, sub948]
  rfl
theorem sub950 (p : Pattern) : d28 (change p 71 none) = d28 p := by
  change (if p 162 then d27 (change p 71 none) else d21 (change p 71 none)) = d28 p
  rw [sub949, sub942]
  rfl
theorem sub951 (p : Pattern) : d29 (change p 71 none) = d29 p := by
  change (if p 161 then d28 (change p 71 none) else d22 (change p 71 none)) = d29 p
  rw [sub950, sub943]
  rfl
theorem sub952 (p : Pattern) : d2 (change p 71 none) = d2 p := by
  rfl
theorem sub953 (p : Pattern) : d30 (change p 71 none) = d30 p := by
  change (if p 247 then d12 (change p 71 none) else d2 (change p 71 none)) = d30 p
  rw [sub932, sub952]
  rfl
theorem sub954 (p : Pattern) : d31 (change p 71 none) = d31 p := by
  change (if p 246 then d30 (change p 71 none) else d2 (change p 71 none)) = d31 p
  rw [sub953, sub952]
  rfl
theorem sub955 (p : Pattern) : d32 (change p 71 none) = d32 p := by
  change (if p 204 then d12 (change p 71 none) else d31 (change p 71 none)) = d32 p
  rw [sub932, sub954]
  rfl
theorem sub956 (p : Pattern) : d33 (change p 71 none) = d33 p := by
  change (if p 182 then d32 (change p 71 none) else d14 (change p 71 none)) = d33 p
  rw [sub955, sub934]
  rfl
theorem sub957 (p : Pattern) : d6 (change p 71 none) = d6 p := by
  rfl
theorem sub958 (p : Pattern) : d34 (change p 71 none) = d34 p := by
  change (if p 247 then d12 (change p 71 none) else d6 (change p 71 none)) = d34 p
  rw [sub932, sub957]
  rfl
theorem sub959 (p : Pattern) : d35 (change p 71 none) = d35 p := by
  change (if p 246 then d34 (change p 71 none) else d6 (change p 71 none)) = d35 p
  rw [sub958, sub957]
  rfl
end NetHack.Sokoban22Refined85
