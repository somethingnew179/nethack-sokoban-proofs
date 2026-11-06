/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions49
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6000 (p : Pattern) : d702 (change p 141 none) = d297 p := by
  change d297 (change p 141 none) = d297 p
  exact sub5999 p
theorem sub6001 (p : Pattern) : d703 (change p 141 none) = d4811 p := by
  change (if p 138 then d702 (change p 141 none) else d701 (change p 141 none)) = d4811 p
  rw [sub6000, sub5992]
  rfl
theorem sub6002 (p : Pattern) : d704 (change p 141 none) = d4812 p := by
  change (if p 138 then d12 (change p 141 none) else d702 (change p 141 none)) = d4812 p
  rw [sub5820, sub6000]
  rfl
theorem sub6003 (p : Pattern) : d705 (change p 141 none) = d4813 p := by
  change (if p 116 then d704 (change p 141 none) else d703 (change p 141 none)) = d4813 p
  rw [sub6002, sub6001]
  rfl
theorem sub6004 (p : Pattern) : d706 (change p 141 none) = d4814 p := by
  change (if p 115 then d705 (change p 141 none) else d700 (change p 141 none)) = d4814 p
  rw [sub6003, sub5977]
  rfl
theorem sub6005 (p : Pattern) : d707 (change p 141 none) = d4815 p := by
  change (if p 71 then d706 (change p 141 none) else d666 (change p 141 none)) = d4815 p
  rw [sub6004, sub5893]
  rfl
theorem sub6006 (p : Pattern) : d708 (change p 141 none) = d4816 p := by
  change (if p 49 then d707 (change p 141 none) else d679 (change p 141 none)) = d4816 p
  rw [sub6005, sub5906]
  rfl
theorem sub6007 (p : Pattern) : d709 (change p 141 none) = d4817 p := by
  change (if p 48 then d708 (change p 141 none) else d694 (change p 141 none)) = d4817 p
  rw [sub6006, sub5971]
  rfl
theorem sub6008 (p : Pattern) : d0 (change p 162 (some 161)) = d0 p := by
  rfl
theorem sub6009 (p : Pattern) : d12 (change p 162 (some 161)) = d12 p := by
  rfl
theorem sub6010 (p : Pattern) : d13 (change p 162 (some 161)) = d13 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d0 (change p 162 (some 161))) = d13 p
  rw [sub6009, sub6008]
  rfl
theorem sub6011 (p : Pattern) : d14 (change p 162 (some 161)) = d14 p := by
  change (if p 246 then d13 (change p 162 (some 161)) else d0 (change p 162 (some 161))) = d14 p
  rw [sub6010, sub6008]
  rfl
theorem sub6012 (p : Pattern) : d15 (change p 162 (some 161)) = d15 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d14 (change p 162 (some 161))) = d15 p
  rw [sub6009, sub6011]
  rfl
theorem sub6013 (p : Pattern) : d16 (change p 162 (some 161)) = d16 p := by
  change (if p 182 then d15 (change p 162 (some 161)) else d14 (change p 162 (some 161))) = d16 p
  rw [sub6012, sub6011]
  rfl
theorem sub6014 (p : Pattern) : d2 (change p 162 (some 161)) = d2 p := by
  rfl
theorem sub6015 (p : Pattern) : d30 (change p 162 (some 161)) = d30 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d2 (change p 162 (some 161))) = d30 p
  rw [sub6009, sub6014]
  rfl
theorem sub6016 (p : Pattern) : d31 (change p 162 (some 161)) = d31 p := by
  change (if p 246 then d30 (change p 162 (some 161)) else d2 (change p 162 (some 161))) = d31 p
  rw [sub6015, sub6014]
  rfl
theorem sub6017 (p : Pattern) : d32 (change p 162 (some 161)) = d32 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d31 (change p 162 (some 161))) = d32 p
  rw [sub6009, sub6016]
  rfl
theorem sub6018 (p : Pattern) : d33 (change p 162 (some 161)) = d33 p := by
  change (if p 182 then d32 (change p 162 (some 161)) else d14 (change p 162 (some 161))) = d33 p
  rw [sub6017, sub6011]
  rfl
theorem sub6019 (p : Pattern) : d950 (change p 162 (some 161)) = d950 p := by
  change (if p 163 then d33 (change p 162 (some 161)) else d16 (change p 162 (some 161))) = d950 p
  rw [sub6018, sub6013]
  rfl
theorem sub6020 (p : Pattern) : d951 (change p 162 (some 161)) = d950 p := by
  change d950 (change p 162 (some 161)) = d950 p
  exact sub6019 p
theorem sub6021 (p : Pattern) : d952 (change p 162 (some 161)) = d950 p := by
  change d951 (change p 162 (some 161)) = d950 p
  exact sub6020 p
theorem sub6022 (p : Pattern) : d46 (change p 162 (some 161)) = d46 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d14 (change p 162 (some 161))) = d46 p
  rw [sub6009, sub6011]
  rfl
theorem sub6023 (p : Pattern) : d4 (change p 162 (some 161)) = d4 p := by
  rfl
theorem sub6024 (p : Pattern) : d17 (change p 162 (some 161)) = d17 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d4 (change p 162 (some 161))) = d17 p
  rw [sub6009, sub6023]
  rfl
theorem sub6025 (p : Pattern) : d18 (change p 162 (some 161)) = d18 p := by
  change (if p 246 then d17 (change p 162 (some 161)) else d4 (change p 162 (some 161))) = d18 p
  rw [sub6024, sub6023]
  rfl
theorem sub6026 (p : Pattern) : d43 (change p 162 (some 161)) = d43 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d18 (change p 162 (some 161))) = d43 p
  rw [sub6009, sub6025]
  rfl
theorem sub6027 (p : Pattern) : d47 (change p 162 (some 161)) = d47 p := by
  change (if p 163 then d43 (change p 162 (some 161)) else d46 (change p 162 (some 161))) = d47 p
  rw [sub6026, sub6022]
  rfl
theorem sub6028 (p : Pattern) : d954 (change p 162 (some 161)) = d47 p := by
  change d47 (change p 162 (some 161)) = d47 p
  exact sub6027 p
theorem sub6029 (p : Pattern) : d955 (change p 162 (some 161)) = d47 p := by
  change d954 (change p 162 (some 161)) = d47 p
  exact sub6028 p
theorem sub6030 (p : Pattern) : d956 (change p 162 (some 161)) = d4818 p := by
  change (if p 160 then d955 (change p 162 (some 161)) else d952 (change p 162 (some 161))) = d4818 p
  rw [sub6029, sub6021]
  rfl
theorem sub6031 (p : Pattern) : d53 (change p 162 (some 161)) = d53 p := by
  change (if p 182 then d32 (change p 162 (some 161)) else d31 (change p 162 (some 161))) = d53 p
  rw [sub6017, sub6016]
  rfl
theorem sub6032 (p : Pattern) : d19 (change p 162 (some 161)) = d19 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d18 (change p 162 (some 161))) = d19 p
  rw [sub6009, sub6025]
  rfl
theorem sub6033 (p : Pattern) : d795 (change p 162 (some 161)) = d795 p := by
  change (if p 182 then d19 (change p 162 (some 161)) else d31 (change p 162 (some 161))) = d795 p
  rw [sub6032, sub6016]
  rfl
theorem sub6034 (p : Pattern) : d796 (change p 162 (some 161)) = d796 p := by
  change (if p 163 then d795 (change p 162 (some 161)) else d53 (change p 162 (some 161))) = d796 p
  rw [sub6033, sub6031]
  rfl
theorem sub6035 (p : Pattern) : d958 (change p 162 (some 161)) = d796 p := by
  change d796 (change p 162 (some 161)) = d796 p
  exact sub6034 p
theorem sub6036 (p : Pattern) : d959 (change p 162 (some 161)) = d796 p := by
  change d958 (change p 162 (some 161)) = d796 p
  exact sub6035 p
theorem sub6037 (p : Pattern) : d66 (change p 162 (some 161)) = d66 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d31 (change p 162 (some 161))) = d66 p
  rw [sub6009, sub6016]
  rfl
theorem sub6038 (p : Pattern) : d6 (change p 162 (some 161)) = d6 p := by
  rfl
theorem sub6039 (p : Pattern) : d34 (change p 162 (some 161)) = d34 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d6 (change p 162 (some 161))) = d34 p
  rw [sub6009, sub6038]
  rfl
theorem sub6040 (p : Pattern) : d35 (change p 162 (some 161)) = d35 p := by
  change (if p 246 then d34 (change p 162 (some 161)) else d6 (change p 162 (some 161))) = d35 p
  rw [sub6039, sub6038]
  rfl
theorem sub6041 (p : Pattern) : d173 (change p 162 (some 161)) = d173 p := by
  change (if p 182 then d12 (change p 162 (some 161)) else d35 (change p 162 (some 161))) = d173 p
  rw [sub6009, sub6040]
  rfl
theorem sub6042 (p : Pattern) : d176 (change p 162 (some 161)) = d176 p := by
  change (if p 163 then d173 (change p 162 (some 161)) else d66 (change p 162 (some 161))) = d176 p
  rw [sub6041, sub6037]
  rfl
theorem sub6043 (p : Pattern) : d961 (change p 162 (some 161)) = d176 p := by
  change d176 (change p 162 (some 161)) = d176 p
  exact sub6042 p
theorem sub6044 (p : Pattern) : d962 (change p 162 (some 161)) = d176 p := by
  change d961 (change p 162 (some 161)) = d176 p
  exact sub6043 p
theorem sub6045 (p : Pattern) : d963 (change p 162 (some 161)) = d4819 p := by
  change (if p 160 then d962 (change p 162 (some 161)) else d959 (change p 162 (some 161))) = d4819 p
  rw [sub6044, sub6036]
  rfl
theorem sub6046 (p : Pattern) : d964 (change p 162 (some 161)) = d4820 p := by
  change (if p 141 then d963 (change p 162 (some 161)) else d956 (change p 162 (some 161))) = d4820 p
  rw [sub6045, sub6030]
  rfl
theorem sub6047 (p : Pattern) : d54 (change p 162 (some 161)) = d54 p := by
  change (if p 163 then d53 (change p 162 (some 161)) else d16 (change p 162 (some 161))) = d54 p
  rw [sub6031, sub6013]
  rfl
theorem sub6048 (p : Pattern) : d966 (change p 162 (some 161)) = d54 p := by
  change d54 (change p 162 (some 161)) = d54 p
  exact sub6047 p
theorem sub6049 (p : Pattern) : d967 (change p 162 (some 161)) = d54 p := by
  change d966 (change p 162 (some 161)) = d54 p
  exact sub6048 p
theorem sub6050 (p : Pattern) : d969 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6051 (p : Pattern) : d970 (change p 162 (some 161)) = d4821 p := by
  change (if p 160 then d969 (change p 162 (some 161)) else d967 (change p 162 (some 161))) = d4821 p
  rw [sub6050, sub6049]
  rfl
theorem sub6052 (p : Pattern) : d20 (change p 162 (some 161)) = d20 p := by
  change (if p 182 then d19 (change p 162 (some 161)) else d18 (change p 162 (some 161))) = d20 p
  rw [sub6032, sub6025]
  rfl
theorem sub6053 (p : Pattern) : d808 (change p 162 (some 161)) = d808 p := by
  change (if p 163 then d20 (change p 162 (some 161)) else d53 (change p 162 (some 161))) = d808 p
  rw [sub6052, sub6031]
  rfl
theorem sub6054 (p : Pattern) : d972 (change p 162 (some 161)) = d808 p := by
  change d808 (change p 162 (some 161)) = d808 p
  exact sub6053 p
theorem sub6055 (p : Pattern) : d973 (change p 162 (some 161)) = d808 p := by
  change d972 (change p 162 (some 161)) = d808 p
  exact sub6054 p
theorem sub6056 (p : Pattern) : d974 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6057 (p : Pattern) : d975 (change p 162 (some 161)) = d4822 p := by
  change (if p 160 then d974 (change p 162 (some 161)) else d973 (change p 162 (some 161))) = d4822 p
  rw [sub6056, sub6055]
  rfl
theorem sub6058 (p : Pattern) : d976 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d975 (change p 162 (some 161)) else d970 (change p 162 (some 161))) = d4823 p
  rw [sub6057, sub6051]
  rfl
theorem sub6059 (p : Pattern) : d977 (change p 162 (some 161)) = d4824 p := by
  change (if p 138 then d976 (change p 162 (some 161)) else d964 (change p 162 (some 161))) = d4824 p
  rw [sub6058, sub6046]
  rfl
theorem sub6060 (p : Pattern) : d979 (change p 162 (some 161)) = d54 p := by
  change d966 (change p 162 (some 161)) = d54 p
  exact sub6048 p
theorem sub6061 (p : Pattern) : d980 (change p 162 (some 161)) = d4821 p := by
  change (if p 160 then d969 (change p 162 (some 161)) else d979 (change p 162 (some 161))) = d4821 p
  rw [sub6050, sub6060]
  rfl
theorem sub6062 (p : Pattern) : d982 (change p 162 (some 161)) = d808 p := by
  change d972 (change p 162 (some 161)) = d808 p
  exact sub6054 p
theorem sub6063 (p : Pattern) : d983 (change p 162 (some 161)) = d4822 p := by
  change (if p 160 then d974 (change p 162 (some 161)) else d982 (change p 162 (some 161))) = d4822 p
  rw [sub6056, sub6062]
  rfl
theorem sub6064 (p : Pattern) : d984 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d983 (change p 162 (some 161)) else d980 (change p 162 (some 161))) = d4823 p
  rw [sub6063, sub6061]
  rfl
theorem sub6065 (p : Pattern) : d11 (change p 162 (some 161)) = d11 p := by
  rfl
theorem sub6066 (p : Pattern) : d39 (change p 162 (some 161)) = d39 p := by
  change (if p 247 then d12 (change p 162 (some 161)) else d11 (change p 162 (some 161))) = d39 p
  rw [sub6009, sub6065]
  rfl
theorem sub6067 (p : Pattern) : d40 (change p 162 (some 161)) = d40 p := by
  change (if p 246 then d39 (change p 162 (some 161)) else d11 (change p 162 (some 161))) = d40 p
  rw [sub6066, sub6065]
  rfl
theorem sub6068 (p : Pattern) : d41 (change p 162 (some 161)) = d41 p := by
  change (if p 204 then d12 (change p 162 (some 161)) else d40 (change p 162 (some 161))) = d41 p
  rw [sub6009, sub6067]
  rfl
theorem sub6069 (p : Pattern) : d62 (change p 162 (some 161)) = d62 p := by
  change (if p 182 then d41 (change p 162 (some 161)) else d40 (change p 162 (some 161))) = d62 p
  rw [sub6068, sub6067]
  rfl
theorem sub6070 (p : Pattern) : d63 (change p 162 (some 161)) = d63 p := by
  change (if p 163 then d12 (change p 162 (some 161)) else d62 (change p 162 (some 161))) = d63 p
  rw [sub6009, sub6069]
  rfl
theorem sub6071 (p : Pattern) : d91 (change p 162 (some 161)) = d63 p := by
  change d63 (change p 162 (some 161)) = d63 p
  exact sub6070 p
theorem sub6072 (p : Pattern) : d986 (change p 162 (some 161)) = d63 p := by
  change d91 (change p 162 (some 161)) = d63 p
  exact sub6071 p
theorem sub6073 (p : Pattern) : d93 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6074 (p : Pattern) : d987 (change p 162 (some 161)) = d4625 p := by
  change (if p 160 then d93 (change p 162 (some 161)) else d986 (change p 162 (some 161))) = d4625 p
  rw [sub6073, sub6072]
  rfl
theorem sub6075 (p : Pattern) : d95 (change p 162 (some 161)) = d12 p := by
  change (if p 160 then d12 (change p 162 (some 161)) else d93 (change p 162 (some 161))) = d12 p
  rw [sub6009, sub6073]
  simp only [ite_self]
theorem sub6076 (p : Pattern) : d988 (change p 162 (some 161)) = d4626 p := by
  change (if p 141 then d95 (change p 162 (some 161)) else d987 (change p 162 (some 161))) = d4626 p
  rw [sub6075, sub6074]
  rfl
theorem sub6077 (p : Pattern) : d989 (change p 162 (some 161)) = d4825 p := by
  change (if p 138 then d988 (change p 162 (some 161)) else d984 (change p 162 (some 161))) = d4825 p
  rw [sub6076, sub6064]
  rfl
theorem sub6078 (p : Pattern) : d990 (change p 162 (some 161)) = d4826 p := by
  change (if p 116 then d989 (change p 162 (some 161)) else d977 (change p 162 (some 161))) = d4826 p
  rw [sub6077, sub6059]
  rfl
theorem sub6079 (p : Pattern) : d992 (change p 162 (some 161)) = d950 p := by
  change d950 (change p 162 (some 161)) = d950 p
  exact sub6019 p
theorem sub6080 (p : Pattern) : d993 (change p 162 (some 161)) = d950 p := by
  change d992 (change p 162 (some 161)) = d950 p
  exact sub6079 p
theorem sub6081 (p : Pattern) : d995 (change p 162 (some 161)) = d47 p := by
  change d954 (change p 162 (some 161)) = d47 p
  exact sub6028 p
theorem sub6082 (p : Pattern) : d996 (change p 162 (some 161)) = d4818 p := by
  change (if p 160 then d995 (change p 162 (some 161)) else d993 (change p 162 (some 161))) = d4818 p
  rw [sub6081, sub6080]
  rfl
theorem sub6083 (p : Pattern) : d960 (change p 162 (some 161)) = d796 p := by
  change d796 (change p 162 (some 161)) = d796 p
  exact sub6034 p
theorem sub6084 (p : Pattern) : d998 (change p 162 (some 161)) = d796 p := by
  change d960 (change p 162 (some 161)) = d796 p
  exact sub6083 p
theorem sub6085 (p : Pattern) : d999 (change p 162 (some 161)) = d4819 p := by
  change (if p 160 then d962 (change p 162 (some 161)) else d998 (change p 162 (some 161))) = d4819 p
  rw [sub6044, sub6084]
  rfl
theorem sub6086 (p : Pattern) : d1000 (change p 162 (some 161)) = d4820 p := by
  change (if p 141 then d999 (change p 162 (some 161)) else d996 (change p 162 (some 161))) = d4820 p
  rw [sub6085, sub6082]
  rfl
theorem sub6087 (p : Pattern) : d1002 (change p 162 (some 161)) = d54 p := by
  change d966 (change p 162 (some 161)) = d54 p
  exact sub6048 p
theorem sub6088 (p : Pattern) : d1003 (change p 162 (some 161)) = d4821 p := by
  change (if p 160 then d969 (change p 162 (some 161)) else d1002 (change p 162 (some 161))) = d4821 p
  rw [sub6050, sub6087]
  rfl
theorem sub6089 (p : Pattern) : d1004 (change p 162 (some 161)) = d808 p := by
  change d972 (change p 162 (some 161)) = d808 p
  exact sub6054 p
theorem sub6090 (p : Pattern) : d1005 (change p 162 (some 161)) = d4822 p := by
  change (if p 160 then d974 (change p 162 (some 161)) else d1004 (change p 162 (some 161))) = d4822 p
  rw [sub6056, sub6089]
  rfl
theorem sub6091 (p : Pattern) : d1006 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d1005 (change p 162 (some 161)) else d1003 (change p 162 (some 161))) = d4823 p
  rw [sub6090, sub6088]
  rfl
theorem sub6092 (p : Pattern) : d1007 (change p 162 (some 161)) = d4824 p := by
  change (if p 138 then d1006 (change p 162 (some 161)) else d1000 (change p 162 (some 161))) = d4824 p
  rw [sub6091, sub6086]
  rfl
theorem sub6093 (p : Pattern) : d1009 (change p 162 (some 161)) = d54 p := by
  change d966 (change p 162 (some 161)) = d54 p
  exact sub6048 p
theorem sub6094 (p : Pattern) : d1010 (change p 162 (some 161)) = d4821 p := by
  change (if p 160 then d969 (change p 162 (some 161)) else d1009 (change p 162 (some 161))) = d4821 p
  rw [sub6050, sub6093]
  rfl
theorem sub6095 (p : Pattern) : d1011 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d1005 (change p 162 (some 161)) else d1010 (change p 162 (some 161))) = d4823 p
  rw [sub6090, sub6094]
  rfl
theorem sub6096 (p : Pattern) : d1012 (change p 162 (some 161)) = d4827 p := by
  change (if p 138 then d12 (change p 162 (some 161)) else d1011 (change p 162 (some 161))) = d4827 p
  rw [sub6009, sub6095]
  rfl
theorem sub6097 (p : Pattern) : d1013 (change p 162 (some 161)) = d4828 p := by
  change (if p 116 then d1012 (change p 162 (some 161)) else d1007 (change p 162 (some 161))) = d4828 p
  rw [sub6096, sub6092]
  rfl
theorem sub6098 (p : Pattern) : d1014 (change p 162 (some 161)) = d4829 p := by
  change (if p 115 then d1013 (change p 162 (some 161)) else d990 (change p 162 (some 161))) = d4829 p
  rw [sub6097, sub6078]
  rfl
theorem sub6099 (p : Pattern) : d1016 (change p 162 (some 161)) = d950 p := by
  change d950 (change p 162 (some 161)) = d950 p
  exact sub6019 p
theorem sub6100 (p : Pattern) : d1017 (change p 162 (some 161)) = d950 p := by
  change d1016 (change p 162 (some 161)) = d950 p
  exact sub6099 p
theorem sub6101 (p : Pattern) : d1019 (change p 162 (some 161)) = d47 p := by
  change d954 (change p 162 (some 161)) = d47 p
  exact sub6028 p
theorem sub6102 (p : Pattern) : d1020 (change p 162 (some 161)) = d4818 p := by
  change (if p 160 then d1019 (change p 162 (some 161)) else d1017 (change p 162 (some 161))) = d4818 p
  rw [sub6101, sub6100]
  rfl
theorem sub6103 (p : Pattern) : d1022 (change p 162 (some 161)) = d796 p := by
  change d960 (change p 162 (some 161)) = d796 p
  exact sub6083 p
theorem sub6104 (p : Pattern) : d1023 (change p 162 (some 161)) = d4819 p := by
  change (if p 160 then d962 (change p 162 (some 161)) else d1022 (change p 162 (some 161))) = d4819 p
  rw [sub6044, sub6103]
  rfl
theorem sub6105 (p : Pattern) : d1024 (change p 162 (some 161)) = d4820 p := by
  change (if p 141 then d1023 (change p 162 (some 161)) else d1020 (change p 162 (some 161))) = d4820 p
  rw [sub6104, sub6102]
  rfl
theorem sub6106 (p : Pattern) : d1026 (change p 162 (some 161)) = d54 p := by
  change d966 (change p 162 (some 161)) = d54 p
  exact sub6048 p
theorem sub6107 (p : Pattern) : d1027 (change p 162 (some 161)) = d4821 p := by
  change (if p 160 then d969 (change p 162 (some 161)) else d1026 (change p 162 (some 161))) = d4821 p
  rw [sub6050, sub6106]
  rfl
theorem sub6108 (p : Pattern) : d1028 (change p 162 (some 161)) = d4823 p := by
  change (if p 141 then d1005 (change p 162 (some 161)) else d1027 (change p 162 (some 161))) = d4823 p
  rw [sub6090, sub6107]
  rfl
theorem sub6109 (p : Pattern) : d1029 (change p 162 (some 161)) = d4824 p := by
  change (if p 138 then d1028 (change p 162 (some 161)) else d1024 (change p 162 (some 161))) = d4824 p
  rw [sub6108, sub6105]
  rfl
theorem sub6110 (p : Pattern) : d1030 (change p 162 (some 161)) = d4825 p := by
  change (if p 138 then d988 (change p 162 (some 161)) else d976 (change p 162 (some 161))) = d4825 p
  rw [sub6076, sub6058]
  rfl
theorem sub6111 (p : Pattern) : d1031 (change p 162 (some 161)) = d4826 p := by
  change (if p 116 then d1030 (change p 162 (some 161)) else d1029 (change p 162 (some 161))) = d4826 p
  rw [sub6110, sub6109]
  rfl
theorem sub6112 (p : Pattern) : d1032 (change p 162 (some 161)) = d950 p := by
  change d992 (change p 162 (some 161)) = d950 p
  exact sub6079 p
theorem sub6113 (p : Pattern) : d1033 (change p 162 (some 161)) = d4818 p := by
  change (if p 160 then d995 (change p 162 (some 161)) else d1032 (change p 162 (some 161))) = d4818 p
  rw [sub6081, sub6112]
  rfl
theorem sub6114 (p : Pattern) : d1034 (change p 162 (some 161)) = d796 p := by
  change d960 (change p 162 (some 161)) = d796 p
  exact sub6083 p
theorem sub6115 (p : Pattern) : d1035 (change p 162 (some 161)) = d4819 p := by
  change (if p 160 then d962 (change p 162 (some 161)) else d1034 (change p 162 (some 161))) = d4819 p
  rw [sub6044, sub6114]
  rfl
theorem sub6116 (p : Pattern) : d1036 (change p 162 (some 161)) = d4820 p := by
  change (if p 141 then d1035 (change p 162 (some 161)) else d1033 (change p 162 (some 161))) = d4820 p
  rw [sub6115, sub6113]
  rfl
theorem sub6117 (p : Pattern) : d1037 (change p 162 (some 161)) = d4824 p := by
  change (if p 138 then d1006 (change p 162 (some 161)) else d1036 (change p 162 (some 161))) = d4824 p
  rw [sub6091, sub6116]
  rfl
theorem sub6118 (p : Pattern) : d1038 (change p 162 (some 161)) = d4827 p := by
  change (if p 138 then d12 (change p 162 (some 161)) else d1006 (change p 162 (some 161))) = d4827 p
  rw [sub6009, sub6091]
  rfl
theorem sub6119 (p : Pattern) : d1039 (change p 162 (some 161)) = d4828 p := by
  change (if p 116 then d1038 (change p 162 (some 161)) else d1037 (change p 162 (some 161))) = d4828 p
  rw [sub6118, sub6117]
  rfl
end NetHack.Sokoban22Refined85
