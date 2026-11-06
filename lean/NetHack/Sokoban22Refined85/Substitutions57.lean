/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions56
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6840 (p : Pattern) : d23 (change p 10000 (some 182)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d9 (change p 10000 (some 182))) = d23 p
  rw [sub6827, sub6839]
  rfl
theorem sub6841 (p : Pattern) : d24 (change p 10000 (some 182)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 182)) else d9 (change p 10000 (some 182))) = d24 p
  rw [sub6840, sub6839]
  rfl
theorem sub6842 (p : Pattern) : d25 (change p 10000 (some 182)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d24 (change p 10000 (some 182))) = d25 p
  rw [sub6827, sub6841]
  rfl
theorem sub6843 (p : Pattern) : d26 (change p 10000 (some 182)) = d25 p := by
  change d25 (change p 10000 (some 182)) = d25 p
  exact sub6842 p
theorem sub6844 (p : Pattern) : d27 (change p 10000 (some 182)) = d4211 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d26 (change p 10000 (some 182))) = d4211 p
  rw [sub6827, sub6843]
  rfl
theorem sub6845 (p : Pattern) : d28 (change p 10000 (some 182)) = d4212 p := by
  change (if p 162 then d27 (change p 10000 (some 182)) else d21 (change p 10000 (some 182))) = d4212 p
  rw [sub6844, sub6837]
  rfl
theorem sub6846 (p : Pattern) : d29 (change p 10000 (some 182)) = d4213 p := by
  change (if p 161 then d28 (change p 10000 (some 182)) else d22 (change p 10000 (some 182))) = d4213 p
  rw [sub6845, sub6838]
  rfl
theorem sub6847 (p : Pattern) : d2 (change p 10000 (some 182)) = d2 p := by
  rfl
theorem sub6848 (p : Pattern) : d30 (change p 10000 (some 182)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d2 (change p 10000 (some 182))) = d30 p
  rw [sub6827, sub6847]
  rfl
theorem sub6849 (p : Pattern) : d31 (change p 10000 (some 182)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 182)) else d2 (change p 10000 (some 182))) = d31 p
  rw [sub6848, sub6847]
  rfl
theorem sub6850 (p : Pattern) : d32 (change p 10000 (some 182)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d31 (change p 10000 (some 182))) = d32 p
  rw [sub6827, sub6849]
  rfl
theorem sub6851 (p : Pattern) : d33 (change p 10000 (some 182)) = d32 p := by
  change d32 (change p 10000 (some 182)) = d32 p
  exact sub6850 p
theorem sub6852 (p : Pattern) : d6 (change p 10000 (some 182)) = d6 p := by
  rfl
theorem sub6853 (p : Pattern) : d34 (change p 10000 (some 182)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d6 (change p 10000 (some 182))) = d34 p
  rw [sub6827, sub6852]
  rfl
theorem sub6854 (p : Pattern) : d35 (change p 10000 (some 182)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 182)) else d6 (change p 10000 (some 182))) = d35 p
  rw [sub6853, sub6852]
  rfl
theorem sub6855 (p : Pattern) : d36 (change p 10000 (some 182)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d35 (change p 10000 (some 182))) = d36 p
  rw [sub6827, sub6854]
  rfl
theorem sub6856 (p : Pattern) : d37 (change p 10000 (some 182)) = d36 p := by
  change d36 (change p 10000 (some 182)) = d36 p
  exact sub6855 p
theorem sub6857 (p : Pattern) : d38 (change p 10000 (some 182)) = d4255 p := by
  change (if p 163 then d37 (change p 10000 (some 182)) else d33 (change p 10000 (some 182))) = d4255 p
  rw [sub6856, sub6851]
  rfl
theorem sub6858 (p : Pattern) : d11 (change p 10000 (some 182)) = d11 p := by
  rfl
theorem sub6859 (p : Pattern) : d39 (change p 10000 (some 182)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d11 (change p 10000 (some 182))) = d39 p
  rw [sub6827, sub6858]
  rfl
theorem sub6860 (p : Pattern) : d40 (change p 10000 (some 182)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 182)) else d11 (change p 10000 (some 182))) = d40 p
  rw [sub6859, sub6858]
  rfl
theorem sub6861 (p : Pattern) : d41 (change p 10000 (some 182)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d40 (change p 10000 (some 182))) = d41 p
  rw [sub6827, sub6860]
  rfl
theorem sub6862 (p : Pattern) : d42 (change p 10000 (some 182)) = d41 p := by
  change d41 (change p 10000 (some 182)) = d41 p
  exact sub6861 p
theorem sub6863 (p : Pattern) : d43 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6864 (p : Pattern) : d44 (change p 10000 (some 182)) = d4218 p := by
  change (if p 163 then d43 (change p 10000 (some 182)) else d42 (change p 10000 (some 182))) = d4218 p
  rw [sub6863, sub6862]
  rfl
theorem sub6865 (p : Pattern) : d45 (change p 10000 (some 182)) = d4257 p := by
  change (if p 162 then d44 (change p 10000 (some 182)) else d38 (change p 10000 (some 182))) = d4257 p
  rw [sub6864, sub6857]
  rfl
theorem sub6866 (p : Pattern) : d46 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6867 (p : Pattern) : d47 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d43 (change p 10000 (some 182)) else d46 (change p 10000 (some 182))) = d12 p
  rw [sub6863, sub6866]
  simp only [ite_self]
theorem sub6868 (p : Pattern) : d48 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6869 (p : Pattern) : d49 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d48 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6868]
  simp only [ite_self]
theorem sub6870 (p : Pattern) : d50 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d49 (change p 10000 (some 182)) else d47 (change p 10000 (some 182))) = d12 p
  rw [sub6869, sub6867]
  simp only [ite_self]
theorem sub6871 (p : Pattern) : d51 (change p 10000 (some 182)) = d4903 p := by
  change (if p 161 then d50 (change p 10000 (some 182)) else d45 (change p 10000 (some 182))) = d4903 p
  rw [sub6870, sub6865]
  rfl
theorem sub6872 (p : Pattern) : d52 (change p 10000 (some 182)) = d4904 p := by
  change (if p 160 then d51 (change p 10000 (some 182)) else d29 (change p 10000 (some 182))) = d4904 p
  rw [sub6871, sub6846]
  rfl
theorem sub6873 (p : Pattern) : d53 (change p 10000 (some 182)) = d32 p := by
  change d32 (change p 10000 (some 182)) = d32 p
  exact sub6850 p
theorem sub6874 (p : Pattern) : d54 (change p 10000 (some 182)) = d4214 p := by
  change (if p 163 then d53 (change p 10000 (some 182)) else d16 (change p 10000 (some 182))) = d4214 p
  rw [sub6873, sub6831]
  rfl
theorem sub6875 (p : Pattern) : d55 (change p 10000 (some 182)) = d4215 p := by
  change (if p 163 then d26 (change p 10000 (some 182)) else d20 (change p 10000 (some 182))) = d4215 p
  rw [sub6843, sub6836]
  rfl
theorem sub6876 (p : Pattern) : d56 (change p 10000 (some 182)) = d4216 p := by
  change (if p 162 then d55 (change p 10000 (some 182)) else d54 (change p 10000 (some 182))) = d4216 p
  rw [sub6875, sub6874]
  rfl
theorem sub6877 (p : Pattern) : d10 (change p 10000 (some 182)) = d10 p := by
  rfl
theorem sub6878 (p : Pattern) : d57 (change p 10000 (some 182)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d10 (change p 10000 (some 182))) = d57 p
  rw [sub6827, sub6877]
  rfl
theorem sub6879 (p : Pattern) : d58 (change p 10000 (some 182)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 182)) else d10 (change p 10000 (some 182))) = d58 p
  rw [sub6878, sub6877]
  rfl
theorem sub6880 (p : Pattern) : d59 (change p 10000 (some 182)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d58 (change p 10000 (some 182))) = d59 p
  rw [sub6827, sub6879]
  rfl
theorem sub6881 (p : Pattern) : d60 (change p 10000 (some 182)) = d59 p := by
  change d59 (change p 10000 (some 182)) = d59 p
  exact sub6880 p
theorem sub6882 (p : Pattern) : d61 (change p 10000 (some 182)) = d4217 p := by
  change (if p 163 then d60 (change p 10000 (some 182)) else d20 (change p 10000 (some 182))) = d4217 p
  rw [sub6881, sub6836]
  rfl
theorem sub6883 (p : Pattern) : d62 (change p 10000 (some 182)) = d41 p := by
  change d41 (change p 10000 (some 182)) = d41 p
  exact sub6861 p
theorem sub6884 (p : Pattern) : d63 (change p 10000 (some 182)) = d4218 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d62 (change p 10000 (some 182))) = d4218 p
  rw [sub6827, sub6883]
  rfl
theorem sub6885 (p : Pattern) : d64 (change p 10000 (some 182)) = d4219 p := by
  change (if p 162 then d63 (change p 10000 (some 182)) else d61 (change p 10000 (some 182))) = d4219 p
  rw [sub6884, sub6882]
  rfl
theorem sub6886 (p : Pattern) : d65 (change p 10000 (some 182)) = d4220 p := by
  change (if p 161 then d64 (change p 10000 (some 182)) else d56 (change p 10000 (some 182))) = d4220 p
  rw [sub6885, sub6876]
  rfl
theorem sub6887 (p : Pattern) : d66 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6888 (p : Pattern) : d67 (change p 10000 (some 182)) = d4261 p := by
  change (if p 163 then d66 (change p 10000 (some 182)) else d37 (change p 10000 (some 182))) = d4261 p
  rw [sub6887, sub6856]
  rfl
theorem sub6889 (p : Pattern) : d68 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d48 (change p 10000 (some 182)) else d43 (change p 10000 (some 182))) = d12 p
  rw [sub6868, sub6863]
  simp only [ite_self]
theorem sub6890 (p : Pattern) : d69 (change p 10000 (some 182)) = d4262 p := by
  change (if p 162 then d68 (change p 10000 (some 182)) else d67 (change p 10000 (some 182))) = d4262 p
  rw [sub6889, sub6888]
  rfl
theorem sub6891 (p : Pattern) : d70 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6892 (p : Pattern) : d71 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d70 (change p 10000 (some 182)) else d43 (change p 10000 (some 182))) = d12 p
  rw [sub6891, sub6863]
  simp only [ite_self]
theorem sub6893 (p : Pattern) : d72 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6894 (p : Pattern) : d73 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d72 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6893]
  simp only [ite_self]
theorem sub6895 (p : Pattern) : d74 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d73 (change p 10000 (some 182)) else d71 (change p 10000 (some 182))) = d12 p
  rw [sub6894, sub6892]
  simp only [ite_self]
theorem sub6896 (p : Pattern) : d75 (change p 10000 (some 182)) = d4905 p := by
  change (if p 161 then d74 (change p 10000 (some 182)) else d69 (change p 10000 (some 182))) = d4905 p
  rw [sub6895, sub6890]
  rfl
theorem sub6897 (p : Pattern) : d76 (change p 10000 (some 182)) = d4906 p := by
  change (if p 160 then d75 (change p 10000 (some 182)) else d65 (change p 10000 (some 182))) = d4906 p
  rw [sub6896, sub6886]
  rfl
theorem sub6898 (p : Pattern) : d77 (change p 10000 (some 182)) = d4907 p := by
  change (if p 141 then d76 (change p 10000 (some 182)) else d52 (change p 10000 (some 182))) = d4907 p
  rw [sub6897, sub6872]
  rfl
theorem sub6899 (p : Pattern) : d78 (change p 10000 (some 182)) = d36 p := by
  change d36 (change p 10000 (some 182)) = d36 p
  exact sub6855 p
theorem sub6900 (p : Pattern) : d79 (change p 10000 (some 182)) = d4255 p := by
  change (if p 163 then d78 (change p 10000 (some 182)) else d53 (change p 10000 (some 182))) = d4255 p
  rw [sub6899, sub6873]
  rfl
theorem sub6901 (p : Pattern) : d80 (change p 10000 (some 182)) = d4257 p := by
  change (if p 162 then d63 (change p 10000 (some 182)) else d79 (change p 10000 (some 182))) = d4257 p
  rw [sub6884, sub6900]
  rfl
theorem sub6902 (p : Pattern) : d81 (change p 10000 (some 182)) = d4903 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d80 (change p 10000 (some 182))) = d4903 p
  rw [sub6827, sub6901]
  rfl
theorem sub6903 (p : Pattern) : d82 (change p 10000 (some 182)) = d4904 p := by
  change (if p 160 then d81 (change p 10000 (some 182)) else d29 (change p 10000 (some 182))) = d4904 p
  rw [sub6902, sub6846]
  rfl
theorem sub6904 (p : Pattern) : d83 (change p 10000 (some 182)) = d4261 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d78 (change p 10000 (some 182))) = d4261 p
  rw [sub6827, sub6899]
  rfl
theorem sub6905 (p : Pattern) : d84 (change p 10000 (some 182)) = d4262 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d83 (change p 10000 (some 182))) = d4262 p
  rw [sub6827, sub6904]
  rfl
theorem sub6906 (p : Pattern) : d85 (change p 10000 (some 182)) = d4905 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d84 (change p 10000 (some 182))) = d4905 p
  rw [sub6827, sub6905]
  rfl
theorem sub6907 (p : Pattern) : d86 (change p 10000 (some 182)) = d4906 p := by
  change (if p 160 then d85 (change p 10000 (some 182)) else d65 (change p 10000 (some 182))) = d4906 p
  rw [sub6906, sub6886]
  rfl
theorem sub6908 (p : Pattern) : d87 (change p 10000 (some 182)) = d4907 p := by
  change (if p 141 then d86 (change p 10000 (some 182)) else d82 (change p 10000 (some 182))) = d4907 p
  rw [sub6907, sub6903]
  rfl
theorem sub6909 (p : Pattern) : d88 (change p 10000 (some 182)) = d4907 p := by
  change (if p 138 then d87 (change p 10000 (some 182)) else d77 (change p 10000 (some 182))) = d4907 p
  rw [sub6908, sub6898]
  simp only [ite_self]
theorem sub6910 (p : Pattern) : d89 (change p 10000 (some 182)) = d4222 p := by
  change (if p 163 then d62 (change p 10000 (some 182)) else d26 (change p 10000 (some 182))) = d4222 p
  rw [sub6883, sub6843]
  rfl
theorem sub6911 (p : Pattern) : d90 (change p 10000 (some 182)) = d4223 p := by
  change (if p 162 then d63 (change p 10000 (some 182)) else d89 (change p 10000 (some 182))) = d4223 p
  rw [sub6884, sub6910]
  rfl
theorem sub6912 (p : Pattern) : d91 (change p 10000 (some 182)) = d4224 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d63 (change p 10000 (some 182))) = d4224 p
  rw [sub6827, sub6884]
  rfl
theorem sub6913 (p : Pattern) : d92 (change p 10000 (some 182)) = d4225 p := by
  change (if p 161 then d91 (change p 10000 (some 182)) else d90 (change p 10000 (some 182))) = d4225 p
  rw [sub6912, sub6911]
  rfl
theorem sub6914 (p : Pattern) : d93 (change p 10000 (some 182)) = d4226 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d91 (change p 10000 (some 182))) = d4226 p
  rw [sub6827, sub6912]
  rfl
theorem sub6915 (p : Pattern) : d94 (change p 10000 (some 182)) = d4908 p := by
  change (if p 160 then d93 (change p 10000 (some 182)) else d92 (change p 10000 (some 182))) = d4908 p
  rw [sub6914, sub6913]
  rfl
theorem sub6916 (p : Pattern) : d95 (change p 10000 (some 182)) = d4909 p := by
  change (if p 160 then d12 (change p 10000 (some 182)) else d93 (change p 10000 (some 182))) = d4909 p
  rw [sub6827, sub6914]
  rfl
theorem sub6917 (p : Pattern) : d96 (change p 10000 (some 182)) = d4910 p := by
  change (if p 141 then d95 (change p 10000 (some 182)) else d94 (change p 10000 (some 182))) = d4910 p
  rw [sub6916, sub6915]
  rfl
theorem sub6918 (p : Pattern) : d97 (change p 10000 (some 182)) = d4911 p := by
  change (if p 138 then d96 (change p 10000 (some 182)) else d87 (change p 10000 (some 182))) = d4911 p
  rw [sub6917, sub6908]
  rfl
theorem sub6919 (p : Pattern) : d98 (change p 10000 (some 182)) = d4912 p := by
  change (if p 116 then d97 (change p 10000 (some 182)) else d88 (change p 10000 (some 182))) = d4912 p
  rw [sub6918, sub6909]
  rfl
theorem sub6920 (p : Pattern) : d99 (change p 10000 (some 182)) = d4913 p := by
  change (if p 138 then d12 (change p 10000 (some 182)) else d87 (change p 10000 (some 182))) = d4913 p
  rw [sub6827, sub6908]
  rfl
theorem sub6921 (p : Pattern) : d100 (change p 10000 (some 182)) = d4914 p := by
  change (if p 116 then d99 (change p 10000 (some 182)) else d88 (change p 10000 (some 182))) = d4914 p
  rw [sub6920, sub6909]
  rfl
theorem sub6922 (p : Pattern) : d101 (change p 10000 (some 182)) = d4915 p := by
  change (if p 115 then d100 (change p 10000 (some 182)) else d98 (change p 10000 (some 182))) = d4915 p
  rw [sub6921, sub6919]
  rfl
theorem sub6923 (p : Pattern) : d1 (change p 10000 (some 182)) = d1 p := by
  rfl
theorem sub6924 (p : Pattern) : d102 (change p 10000 (some 182)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d1 (change p 10000 (some 182))) = d102 p
  rw [sub6827, sub6923]
  rfl
theorem sub6925 (p : Pattern) : d103 (change p 10000 (some 182)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 182)) else d1 (change p 10000 (some 182))) = d103 p
  rw [sub6924, sub6923]
  rfl
theorem sub6926 (p : Pattern) : d104 (change p 10000 (some 182)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d103 (change p 10000 (some 182))) = d104 p
  rw [sub6827, sub6925]
  rfl
theorem sub6927 (p : Pattern) : d105 (change p 10000 (some 182)) = d104 p := by
  change d104 (change p 10000 (some 182)) = d104 p
  exact sub6926 p
theorem sub6928 (p : Pattern) : d5 (change p 10000 (some 182)) = d5 p := by
  rfl
theorem sub6929 (p : Pattern) : d106 (change p 10000 (some 182)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d5 (change p 10000 (some 182))) = d106 p
  rw [sub6827, sub6928]
  rfl
theorem sub6930 (p : Pattern) : d107 (change p 10000 (some 182)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 182)) else d5 (change p 10000 (some 182))) = d107 p
  rw [sub6929, sub6928]
  rfl
theorem sub6931 (p : Pattern) : d108 (change p 10000 (some 182)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d107 (change p 10000 (some 182))) = d108 p
  rw [sub6827, sub6930]
  rfl
theorem sub6932 (p : Pattern) : d109 (change p 10000 (some 182)) = d108 p := by
  change d108 (change p 10000 (some 182)) = d108 p
  exact sub6931 p
theorem sub6933 (p : Pattern) : d110 (change p 10000 (some 182)) = d4233 p := by
  change (if p 163 then d109 (change p 10000 (some 182)) else d105 (change p 10000 (some 182))) = d4233 p
  rw [sub6932, sub6927]
  rfl
theorem sub6934 (p : Pattern) : d111 (change p 10000 (some 182)) = d4234 p := by
  change (if p 162 then d110 (change p 10000 (some 182)) else d105 (change p 10000 (some 182))) = d4234 p
  rw [sub6933, sub6927]
  rfl
theorem sub6935 (p : Pattern) : d112 (change p 10000 (some 182)) = d4235 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d60 (change p 10000 (some 182))) = d4235 p
  rw [sub6827, sub6881]
  rfl
theorem sub6936 (p : Pattern) : d113 (change p 10000 (some 182)) = d4236 p := by
  change (if p 162 then d112 (change p 10000 (some 182)) else d110 (change p 10000 (some 182))) = d4236 p
  rw [sub6935, sub6933]
  rfl
theorem sub6937 (p : Pattern) : d114 (change p 10000 (some 182)) = d4237 p := by
  change (if p 161 then d113 (change p 10000 (some 182)) else d111 (change p 10000 (some 182))) = d4237 p
  rw [sub6936, sub6934]
  rfl
theorem sub6938 (p : Pattern) : d3 (change p 10000 (some 182)) = d3 p := by
  rfl
theorem sub6939 (p : Pattern) : d115 (change p 10000 (some 182)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d3 (change p 10000 (some 182))) = d115 p
  rw [sub6827, sub6938]
  rfl
theorem sub6940 (p : Pattern) : d116 (change p 10000 (some 182)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 182)) else d3 (change p 10000 (some 182))) = d116 p
  rw [sub6939, sub6938]
  rfl
theorem sub6941 (p : Pattern) : d117 (change p 10000 (some 182)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d116 (change p 10000 (some 182))) = d117 p
  rw [sub6827, sub6940]
  rfl
theorem sub6942 (p : Pattern) : d118 (change p 10000 (some 182)) = d117 p := by
  change d117 (change p 10000 (some 182)) = d117 p
  exact sub6941 p
theorem sub6943 (p : Pattern) : d7 (change p 10000 (some 182)) = d7 p := by
  rfl
theorem sub6944 (p : Pattern) : d119 (change p 10000 (some 182)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d7 (change p 10000 (some 182))) = d119 p
  rw [sub6827, sub6943]
  rfl
theorem sub6945 (p : Pattern) : d120 (change p 10000 (some 182)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 182)) else d7 (change p 10000 (some 182))) = d120 p
  rw [sub6944, sub6943]
  rfl
theorem sub6946 (p : Pattern) : d121 (change p 10000 (some 182)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d120 (change p 10000 (some 182))) = d121 p
  rw [sub6827, sub6945]
  rfl
theorem sub6947 (p : Pattern) : d122 (change p 10000 (some 182)) = d121 p := by
  change d121 (change p 10000 (some 182)) = d121 p
  exact sub6946 p
theorem sub6948 (p : Pattern) : d123 (change p 10000 (some 182)) = d4916 p := by
  change (if p 163 then d122 (change p 10000 (some 182)) else d118 (change p 10000 (some 182))) = d4916 p
  rw [sub6947, sub6942]
  rfl
theorem sub6949 (p : Pattern) : d124 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6950 (p : Pattern) : d125 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6951 (p : Pattern) : d126 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d125 (change p 10000 (some 182)) else d124 (change p 10000 (some 182))) = d12 p
  rw [sub6950, sub6949]
  simp only [ite_self]
theorem sub6952 (p : Pattern) : d127 (change p 10000 (some 182)) = d4917 p := by
  change (if p 162 then d126 (change p 10000 (some 182)) else d123 (change p 10000 (some 182))) = d4917 p
  rw [sub6951, sub6948]
  rfl
theorem sub6953 (p : Pattern) : d128 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d70 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6891]
  simp only [ite_self]
theorem sub6954 (p : Pattern) : d129 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d128 (change p 10000 (some 182)) else d126 (change p 10000 (some 182))) = d12 p
  rw [sub6953, sub6951]
  simp only [ite_self]
theorem sub6955 (p : Pattern) : d130 (change p 10000 (some 182)) = d4918 p := by
  change (if p 161 then d129 (change p 10000 (some 182)) else d127 (change p 10000 (some 182))) = d4918 p
  rw [sub6954, sub6952]
  rfl
theorem sub6956 (p : Pattern) : d131 (change p 10000 (some 182)) = d4919 p := by
  change (if p 160 then d130 (change p 10000 (some 182)) else d114 (change p 10000 (some 182))) = d4919 p
  rw [sub6955, sub6937]
  rfl
theorem sub6957 (p : Pattern) : d132 (change p 10000 (some 182)) = d117 p := by
  change d117 (change p 10000 (some 182)) = d117 p
  exact sub6941 p
theorem sub6958 (p : Pattern) : d133 (change p 10000 (some 182)) = d4238 p := by
  change (if p 163 then d132 (change p 10000 (some 182)) else d105 (change p 10000 (some 182))) = d4238 p
  rw [sub6957, sub6927]
  rfl
theorem sub6959 (p : Pattern) : d134 (change p 10000 (some 182)) = d4239 p := by
  change (if p 163 then d60 (change p 10000 (some 182)) else d109 (change p 10000 (some 182))) = d4239 p
  rw [sub6881, sub6932]
  rfl
end NetHack.Sokoban22Refined85
