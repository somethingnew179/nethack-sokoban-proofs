/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5160 (p : Pattern) : d954 (change p 162 (some 163)) = d43 p := by
  change d47 (change p 162 (some 163)) = d43 p
  exact sub5159 p
theorem sub5161 (p : Pattern) : d955 (change p 162 (some 163)) = d4675 p := by
  change (if p 161 then d954 (change p 162 (some 163)) else d953 (change p 162 (some 163))) = d4675 p
  rw [sub5160, sub5154]
  rfl
theorem sub5162 (p : Pattern) : d956 (change p 162 (some 163)) = d4676 p := by
  change (if p 160 then d955 (change p 162 (some 163)) else d952 (change p 162 (some 163))) = d4676 p
  rw [sub5161, sub5153]
  rfl
theorem sub5163 (p : Pattern) : d53 (change p 162 (some 163)) = d53 p := by
  change (if p 182 then d32 (change p 162 (some 163)) else d31 (change p 162 (some 163))) = d53 p
  rw [sub5149, sub5148]
  rfl
theorem sub5164 (p : Pattern) : d54 (change p 162 (some 163)) = d53 p := by
  change d53 (change p 162 (some 163)) = d53 p
  exact sub5163 p
theorem sub5165 (p : Pattern) : d957 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5166 (p : Pattern) : d19 (change p 162 (some 163)) = d19 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d18 (change p 162 (some 163))) = d19 p
  rw [sub5140, sub5157]
  rfl
theorem sub5167 (p : Pattern) : d795 (change p 162 (some 163)) = d795 p := by
  change (if p 182 then d19 (change p 162 (some 163)) else d31 (change p 162 (some 163))) = d795 p
  rw [sub5166, sub5148]
  rfl
theorem sub5168 (p : Pattern) : d796 (change p 162 (some 163)) = d795 p := by
  change d795 (change p 162 (some 163)) = d795 p
  exact sub5167 p
theorem sub5169 (p : Pattern) : d958 (change p 162 (some 163)) = d795 p := by
  change d796 (change p 162 (some 163)) = d795 p
  exact sub5168 p
theorem sub5170 (p : Pattern) : d959 (change p 162 (some 163)) = d4677 p := by
  change (if p 161 then d958 (change p 162 (some 163)) else d957 (change p 162 (some 163))) = d4677 p
  rw [sub5169, sub5165]
  rfl
theorem sub5171 (p : Pattern) : d960 (change p 162 (some 163)) = d795 p := by
  change d796 (change p 162 (some 163)) = d795 p
  exact sub5168 p
theorem sub5172 (p : Pattern) : d6 (change p 162 (some 163)) = d6 p := by
  rfl
theorem sub5173 (p : Pattern) : d34 (change p 162 (some 163)) = d34 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d6 (change p 162 (some 163))) = d34 p
  rw [sub5140, sub5172]
  rfl
theorem sub5174 (p : Pattern) : d35 (change p 162 (some 163)) = d35 p := by
  change (if p 246 then d34 (change p 162 (some 163)) else d6 (change p 162 (some 163))) = d35 p
  rw [sub5173, sub5172]
  rfl
theorem sub5175 (p : Pattern) : d173 (change p 162 (some 163)) = d173 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d35 (change p 162 (some 163))) = d173 p
  rw [sub5140, sub5174]
  rfl
theorem sub5176 (p : Pattern) : d176 (change p 162 (some 163)) = d173 p := by
  change d173 (change p 162 (some 163)) = d173 p
  exact sub5175 p
theorem sub5177 (p : Pattern) : d961 (change p 162 (some 163)) = d173 p := by
  change d176 (change p 162 (some 163)) = d173 p
  exact sub5176 p
theorem sub5178 (p : Pattern) : d962 (change p 162 (some 163)) = d4678 p := by
  change (if p 161 then d961 (change p 162 (some 163)) else d960 (change p 162 (some 163))) = d4678 p
  rw [sub5177, sub5171]
  rfl
theorem sub5179 (p : Pattern) : d963 (change p 162 (some 163)) = d4679 p := by
  change (if p 160 then d962 (change p 162 (some 163)) else d959 (change p 162 (some 163))) = d4679 p
  rw [sub5178, sub5170]
  rfl
theorem sub5180 (p : Pattern) : d964 (change p 162 (some 163)) = d4680 p := by
  change (if p 141 then d963 (change p 162 (some 163)) else d956 (change p 162 (some 163))) = d4680 p
  rw [sub5179, sub5162]
  rfl
theorem sub5181 (p : Pattern) : d965 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5182 (p : Pattern) : d966 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5183 (p : Pattern) : d967 (change p 162 (some 163)) = d4681 p := by
  change (if p 161 then d966 (change p 162 (some 163)) else d965 (change p 162 (some 163))) = d4681 p
  rw [sub5182, sub5181]
  rfl
theorem sub5184 (p : Pattern) : d968 (change p 162 (some 163)) = d53 p := by
  change d53 (change p 162 (some 163)) = d53 p
  exact sub5163 p
theorem sub5185 (p : Pattern) : d969 (change p 162 (some 163)) = d4682 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d968 (change p 162 (some 163))) = d4682 p
  rw [sub5140, sub5184]
  rfl
theorem sub5186 (p : Pattern) : d970 (change p 162 (some 163)) = d4683 p := by
  change (if p 160 then d969 (change p 162 (some 163)) else d967 (change p 162 (some 163))) = d4683 p
  rw [sub5185, sub5183]
  rfl
theorem sub5187 (p : Pattern) : d971 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5188 (p : Pattern) : d20 (change p 162 (some 163)) = d20 p := by
  change (if p 182 then d19 (change p 162 (some 163)) else d18 (change p 162 (some 163))) = d20 p
  rw [sub5166, sub5157]
  rfl
theorem sub5189 (p : Pattern) : d808 (change p 162 (some 163)) = d20 p := by
  change d20 (change p 162 (some 163)) = d20 p
  exact sub5188 p
theorem sub5190 (p : Pattern) : d972 (change p 162 (some 163)) = d20 p := by
  change d808 (change p 162 (some 163)) = d20 p
  exact sub5189 p
theorem sub5191 (p : Pattern) : d973 (change p 162 (some 163)) = d4684 p := by
  change (if p 161 then d972 (change p 162 (some 163)) else d971 (change p 162 (some 163))) = d4684 p
  rw [sub5190, sub5187]
  rfl
theorem sub5192 (p : Pattern) : d974 (change p 162 (some 163)) = d4685 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d972 (change p 162 (some 163))) = d4685 p
  rw [sub5140, sub5190]
  rfl
theorem sub5193 (p : Pattern) : d975 (change p 162 (some 163)) = d4686 p := by
  change (if p 160 then d974 (change p 162 (some 163)) else d973 (change p 162 (some 163))) = d4686 p
  rw [sub5192, sub5191]
  rfl
theorem sub5194 (p : Pattern) : d976 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d975 (change p 162 (some 163)) else d970 (change p 162 (some 163))) = d4687 p
  rw [sub5193, sub5186]
  rfl
theorem sub5195 (p : Pattern) : d977 (change p 162 (some 163)) = d4688 p := by
  change (if p 138 then d976 (change p 162 (some 163)) else d964 (change p 162 (some 163))) = d4688 p
  rw [sub5194, sub5180]
  rfl
theorem sub5196 (p : Pattern) : d978 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5197 (p : Pattern) : d979 (change p 162 (some 163)) = d4681 p := by
  change (if p 161 then d966 (change p 162 (some 163)) else d978 (change p 162 (some 163))) = d4681 p
  rw [sub5182, sub5196]
  rfl
theorem sub5198 (p : Pattern) : d980 (change p 162 (some 163)) = d4683 p := by
  change (if p 160 then d969 (change p 162 (some 163)) else d979 (change p 162 (some 163))) = d4683 p
  rw [sub5185, sub5197]
  rfl
theorem sub5199 (p : Pattern) : d981 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5200 (p : Pattern) : d982 (change p 162 (some 163)) = d4684 p := by
  change (if p 161 then d972 (change p 162 (some 163)) else d981 (change p 162 (some 163))) = d4684 p
  rw [sub5190, sub5199]
  rfl
theorem sub5201 (p : Pattern) : d983 (change p 162 (some 163)) = d4686 p := by
  change (if p 160 then d974 (change p 162 (some 163)) else d982 (change p 162 (some 163))) = d4686 p
  rw [sub5192, sub5200]
  rfl
theorem sub5202 (p : Pattern) : d984 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d983 (change p 162 (some 163)) else d980 (change p 162 (some 163))) = d4687 p
  rw [sub5201, sub5198]
  rfl
theorem sub5203 (p : Pattern) : d11 (change p 162 (some 163)) = d11 p := by
  rfl
theorem sub5204 (p : Pattern) : d39 (change p 162 (some 163)) = d39 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d11 (change p 162 (some 163))) = d39 p
  rw [sub5140, sub5203]
  rfl
theorem sub5205 (p : Pattern) : d40 (change p 162 (some 163)) = d40 p := by
  change (if p 246 then d39 (change p 162 (some 163)) else d11 (change p 162 (some 163))) = d40 p
  rw [sub5204, sub5203]
  rfl
theorem sub5206 (p : Pattern) : d41 (change p 162 (some 163)) = d41 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d40 (change p 162 (some 163))) = d41 p
  rw [sub5140, sub5205]
  rfl
theorem sub5207 (p : Pattern) : d62 (change p 162 (some 163)) = d62 p := by
  change (if p 182 then d41 (change p 162 (some 163)) else d40 (change p 162 (some 163))) = d62 p
  rw [sub5206, sub5205]
  rfl
theorem sub5208 (p : Pattern) : d89 (change p 162 (some 163)) = d62 p := by
  change d62 (change p 162 (some 163)) = d62 p
  exact sub5207 p
theorem sub5209 (p : Pattern) : d985 (change p 162 (some 163)) = d62 p := by
  change d89 (change p 162 (some 163)) = d62 p
  exact sub5208 p
theorem sub5210 (p : Pattern) : d63 (change p 162 (some 163)) = d12 p := by
  change d12 (change p 162 (some 163)) = d12 p
  exact sub5140 p
theorem sub5211 (p : Pattern) : d91 (change p 162 (some 163)) = d12 p := by
  change d63 (change p 162 (some 163)) = d12 p
  exact sub5210 p
theorem sub5212 (p : Pattern) : d986 (change p 162 (some 163)) = d4689 p := by
  change (if p 161 then d91 (change p 162 (some 163)) else d985 (change p 162 (some 163))) = d4689 p
  rw [sub5211, sub5209]
  rfl
theorem sub5213 (p : Pattern) : d93 (change p 162 (some 163)) = d12 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d91 (change p 162 (some 163))) = d12 p
  rw [sub5140, sub5211]
  simp only [ite_self]
theorem sub5214 (p : Pattern) : d987 (change p 162 (some 163)) = d4690 p := by
  change (if p 160 then d93 (change p 162 (some 163)) else d986 (change p 162 (some 163))) = d4690 p
  rw [sub5213, sub5212]
  rfl
theorem sub5215 (p : Pattern) : d95 (change p 162 (some 163)) = d12 p := by
  change (if p 160 then d12 (change p 162 (some 163)) else d93 (change p 162 (some 163))) = d12 p
  rw [sub5140, sub5213]
  simp only [ite_self]
theorem sub5216 (p : Pattern) : d988 (change p 162 (some 163)) = d4691 p := by
  change (if p 141 then d95 (change p 162 (some 163)) else d987 (change p 162 (some 163))) = d4691 p
  rw [sub5215, sub5214]
  rfl
theorem sub5217 (p : Pattern) : d989 (change p 162 (some 163)) = d4692 p := by
  change (if p 138 then d988 (change p 162 (some 163)) else d984 (change p 162 (some 163))) = d4692 p
  rw [sub5216, sub5202]
  rfl
theorem sub5218 (p : Pattern) : d990 (change p 162 (some 163)) = d4693 p := by
  change (if p 116 then d989 (change p 162 (some 163)) else d977 (change p 162 (some 163))) = d4693 p
  rw [sub5217, sub5195]
  rfl
theorem sub5219 (p : Pattern) : d991 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5220 (p : Pattern) : d992 (change p 162 (some 163)) = d33 p := by
  change d950 (change p 162 (some 163)) = d33 p
  exact sub5151 p
theorem sub5221 (p : Pattern) : d993 (change p 162 (some 163)) = d4674 p := by
  change (if p 161 then d992 (change p 162 (some 163)) else d991 (change p 162 (some 163))) = d4674 p
  rw [sub5220, sub5219]
  rfl
theorem sub5222 (p : Pattern) : d994 (change p 162 (some 163)) = d33 p := by
  change d33 (change p 162 (some 163)) = d33 p
  exact sub5150 p
theorem sub5223 (p : Pattern) : d995 (change p 162 (some 163)) = d4675 p := by
  change (if p 161 then d954 (change p 162 (some 163)) else d994 (change p 162 (some 163))) = d4675 p
  rw [sub5160, sub5222]
  rfl
theorem sub5224 (p : Pattern) : d996 (change p 162 (some 163)) = d4676 p := by
  change (if p 160 then d995 (change p 162 (some 163)) else d993 (change p 162 (some 163))) = d4676 p
  rw [sub5223, sub5221]
  rfl
theorem sub5225 (p : Pattern) : d997 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5226 (p : Pattern) : d998 (change p 162 (some 163)) = d4677 p := by
  change (if p 161 then d960 (change p 162 (some 163)) else d997 (change p 162 (some 163))) = d4677 p
  rw [sub5171, sub5225]
  rfl
theorem sub5227 (p : Pattern) : d999 (change p 162 (some 163)) = d4679 p := by
  change (if p 160 then d962 (change p 162 (some 163)) else d998 (change p 162 (some 163))) = d4679 p
  rw [sub5178, sub5226]
  rfl
theorem sub5228 (p : Pattern) : d1000 (change p 162 (some 163)) = d4680 p := by
  change (if p 141 then d999 (change p 162 (some 163)) else d996 (change p 162 (some 163))) = d4680 p
  rw [sub5227, sub5224]
  rfl
theorem sub5229 (p : Pattern) : d1001 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5230 (p : Pattern) : d1002 (change p 162 (some 163)) = d4681 p := by
  change (if p 161 then d966 (change p 162 (some 163)) else d1001 (change p 162 (some 163))) = d4681 p
  rw [sub5182, sub5229]
  rfl
theorem sub5231 (p : Pattern) : d1003 (change p 162 (some 163)) = d4683 p := by
  change (if p 160 then d969 (change p 162 (some 163)) else d1002 (change p 162 (some 163))) = d4683 p
  rw [sub5185, sub5230]
  rfl
theorem sub5232 (p : Pattern) : d1004 (change p 162 (some 163)) = d4684 p := by
  change (if p 161 then d972 (change p 162 (some 163)) else d966 (change p 162 (some 163))) = d4684 p
  rw [sub5190, sub5182]
  rfl
theorem sub5233 (p : Pattern) : d1005 (change p 162 (some 163)) = d4686 p := by
  change (if p 160 then d974 (change p 162 (some 163)) else d1004 (change p 162 (some 163))) = d4686 p
  rw [sub5192, sub5232]
  rfl
theorem sub5234 (p : Pattern) : d1006 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d1005 (change p 162 (some 163)) else d1003 (change p 162 (some 163))) = d4687 p
  rw [sub5233, sub5231]
  rfl
theorem sub5235 (p : Pattern) : d1007 (change p 162 (some 163)) = d4688 p := by
  change (if p 138 then d1006 (change p 162 (some 163)) else d1000 (change p 162 (some 163))) = d4688 p
  rw [sub5234, sub5228]
  rfl
theorem sub5236 (p : Pattern) : d1008 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5237 (p : Pattern) : d1009 (change p 162 (some 163)) = d4681 p := by
  change (if p 161 then d966 (change p 162 (some 163)) else d1008 (change p 162 (some 163))) = d4681 p
  rw [sub5182, sub5236]
  rfl
theorem sub5238 (p : Pattern) : d1010 (change p 162 (some 163)) = d4683 p := by
  change (if p 160 then d969 (change p 162 (some 163)) else d1009 (change p 162 (some 163))) = d4683 p
  rw [sub5185, sub5237]
  rfl
theorem sub5239 (p : Pattern) : d1011 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d1005 (change p 162 (some 163)) else d1010 (change p 162 (some 163))) = d4687 p
  rw [sub5233, sub5238]
  rfl
theorem sub5240 (p : Pattern) : d1012 (change p 162 (some 163)) = d4694 p := by
  change (if p 138 then d12 (change p 162 (some 163)) else d1011 (change p 162 (some 163))) = d4694 p
  rw [sub5140, sub5239]
  rfl
theorem sub5241 (p : Pattern) : d1013 (change p 162 (some 163)) = d4695 p := by
  change (if p 116 then d1012 (change p 162 (some 163)) else d1007 (change p 162 (some 163))) = d4695 p
  rw [sub5240, sub5235]
  rfl
theorem sub5242 (p : Pattern) : d1014 (change p 162 (some 163)) = d4696 p := by
  change (if p 115 then d1013 (change p 162 (some 163)) else d990 (change p 162 (some 163))) = d4696 p
  rw [sub5241, sub5218]
  rfl
theorem sub5243 (p : Pattern) : d1015 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5244 (p : Pattern) : d1016 (change p 162 (some 163)) = d33 p := by
  change d950 (change p 162 (some 163)) = d33 p
  exact sub5151 p
theorem sub5245 (p : Pattern) : d1017 (change p 162 (some 163)) = d4674 p := by
  change (if p 161 then d1016 (change p 162 (some 163)) else d1015 (change p 162 (some 163))) = d4674 p
  rw [sub5244, sub5243]
  rfl
theorem sub5246 (p : Pattern) : d1018 (change p 162 (some 163)) = d33 p := by
  change d33 (change p 162 (some 163)) = d33 p
  exact sub5150 p
theorem sub5247 (p : Pattern) : d1019 (change p 162 (some 163)) = d4675 p := by
  change (if p 161 then d954 (change p 162 (some 163)) else d1018 (change p 162 (some 163))) = d4675 p
  rw [sub5160, sub5246]
  rfl
theorem sub5248 (p : Pattern) : d1020 (change p 162 (some 163)) = d4676 p := by
  change (if p 160 then d1019 (change p 162 (some 163)) else d1017 (change p 162 (some 163))) = d4676 p
  rw [sub5247, sub5245]
  rfl
theorem sub5249 (p : Pattern) : d1021 (change p 162 (some 163)) = d53 p := by
  change d54 (change p 162 (some 163)) = d53 p
  exact sub5164 p
theorem sub5250 (p : Pattern) : d1022 (change p 162 (some 163)) = d4677 p := by
  change (if p 161 then d960 (change p 162 (some 163)) else d1021 (change p 162 (some 163))) = d4677 p
  rw [sub5171, sub5249]
  rfl
theorem sub5251 (p : Pattern) : d1023 (change p 162 (some 163)) = d4679 p := by
  change (if p 160 then d962 (change p 162 (some 163)) else d1022 (change p 162 (some 163))) = d4679 p
  rw [sub5178, sub5250]
  rfl
theorem sub5252 (p : Pattern) : d1024 (change p 162 (some 163)) = d4680 p := by
  change (if p 141 then d1023 (change p 162 (some 163)) else d1020 (change p 162 (some 163))) = d4680 p
  rw [sub5251, sub5248]
  rfl
theorem sub5253 (p : Pattern) : d1025 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5254 (p : Pattern) : d1026 (change p 162 (some 163)) = d4681 p := by
  change (if p 161 then d966 (change p 162 (some 163)) else d1025 (change p 162 (some 163))) = d4681 p
  rw [sub5182, sub5253]
  rfl
theorem sub5255 (p : Pattern) : d1027 (change p 162 (some 163)) = d4683 p := by
  change (if p 160 then d969 (change p 162 (some 163)) else d1026 (change p 162 (some 163))) = d4683 p
  rw [sub5185, sub5254]
  rfl
theorem sub5256 (p : Pattern) : d1028 (change p 162 (some 163)) = d4687 p := by
  change (if p 141 then d1005 (change p 162 (some 163)) else d1027 (change p 162 (some 163))) = d4687 p
  rw [sub5233, sub5255]
  rfl
theorem sub5257 (p : Pattern) : d1029 (change p 162 (some 163)) = d4688 p := by
  change (if p 138 then d1028 (change p 162 (some 163)) else d1024 (change p 162 (some 163))) = d4688 p
  rw [sub5256, sub5252]
  rfl
theorem sub5258 (p : Pattern) : d1030 (change p 162 (some 163)) = d4692 p := by
  change (if p 138 then d988 (change p 162 (some 163)) else d976 (change p 162 (some 163))) = d4692 p
  rw [sub5216, sub5194]
  rfl
theorem sub5259 (p : Pattern) : d1031 (change p 162 (some 163)) = d4693 p := by
  change (if p 116 then d1030 (change p 162 (some 163)) else d1029 (change p 162 (some 163))) = d4693 p
  rw [sub5258, sub5257]
  rfl
theorem sub5260 (p : Pattern) : d1032 (change p 162 (some 163)) = d4674 p := by
  change (if p 161 then d992 (change p 162 (some 163)) else d978 (change p 162 (some 163))) = d4674 p
  rw [sub5220, sub5196]
  rfl
theorem sub5261 (p : Pattern) : d1033 (change p 162 (some 163)) = d4676 p := by
  change (if p 160 then d995 (change p 162 (some 163)) else d1032 (change p 162 (some 163))) = d4676 p
  rw [sub5223, sub5260]
  rfl
theorem sub5262 (p : Pattern) : d1034 (change p 162 (some 163)) = d4677 p := by
  change (if p 161 then d960 (change p 162 (some 163)) else d981 (change p 162 (some 163))) = d4677 p
  rw [sub5171, sub5199]
  rfl
theorem sub5263 (p : Pattern) : d1035 (change p 162 (some 163)) = d4679 p := by
  change (if p 160 then d962 (change p 162 (some 163)) else d1034 (change p 162 (some 163))) = d4679 p
  rw [sub5178, sub5262]
  rfl
theorem sub5264 (p : Pattern) : d1036 (change p 162 (some 163)) = d4680 p := by
  change (if p 141 then d1035 (change p 162 (some 163)) else d1033 (change p 162 (some 163))) = d4680 p
  rw [sub5263, sub5261]
  rfl
theorem sub5265 (p : Pattern) : d1037 (change p 162 (some 163)) = d4688 p := by
  change (if p 138 then d1006 (change p 162 (some 163)) else d1036 (change p 162 (some 163))) = d4688 p
  rw [sub5234, sub5264]
  rfl
theorem sub5266 (p : Pattern) : d1038 (change p 162 (some 163)) = d4694 p := by
  change (if p 138 then d12 (change p 162 (some 163)) else d1006 (change p 162 (some 163))) = d4694 p
  rw [sub5140, sub5234]
  rfl
theorem sub5267 (p : Pattern) : d1039 (change p 162 (some 163)) = d4695 p := by
  change (if p 116 then d1038 (change p 162 (some 163)) else d1037 (change p 162 (some 163))) = d4695 p
  rw [sub5266, sub5265]
  rfl
theorem sub5268 (p : Pattern) : d1040 (change p 162 (some 163)) = d4696 p := by
  change (if p 115 then d1039 (change p 162 (some 163)) else d1031 (change p 162 (some 163))) = d4696 p
  rw [sub5267, sub5259]
  rfl
theorem sub5269 (p : Pattern) : d1041 (change p 162 (some 163)) = d4696 p := by
  change (if p 71 then d1040 (change p 162 (some 163)) else d1014 (change p 162 (some 163))) = d4696 p
  rw [sub5268, sub5242]
  simp only [ite_self]
theorem sub5270 (p : Pattern) : d1 (change p 162 (some 163)) = d1 p := by
  rfl
theorem sub5271 (p : Pattern) : d102 (change p 162 (some 163)) = d102 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d1 (change p 162 (some 163))) = d102 p
  rw [sub5140, sub5270]
  rfl
theorem sub5272 (p : Pattern) : d103 (change p 162 (some 163)) = d103 p := by
  change (if p 246 then d102 (change p 162 (some 163)) else d1 (change p 162 (some 163))) = d103 p
  rw [sub5271, sub5270]
  rfl
theorem sub5273 (p : Pattern) : d104 (change p 162 (some 163)) = d104 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d103 (change p 162 (some 163))) = d104 p
  rw [sub5140, sub5272]
  rfl
theorem sub5274 (p : Pattern) : d105 (change p 162 (some 163)) = d105 p := by
  change (if p 182 then d104 (change p 162 (some 163)) else d103 (change p 162 (some 163))) = d105 p
  rw [sub5273, sub5272]
  rfl
theorem sub5275 (p : Pattern) : d1042 (change p 162 (some 163)) = d105 p := by
  change d105 (change p 162 (some 163)) = d105 p
  exact sub5274 p
theorem sub5276 (p : Pattern) : d3 (change p 162 (some 163)) = d3 p := by
  rfl
theorem sub5277 (p : Pattern) : d115 (change p 162 (some 163)) = d115 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d3 (change p 162 (some 163))) = d115 p
  rw [sub5140, sub5276]
  rfl
theorem sub5278 (p : Pattern) : d116 (change p 162 (some 163)) = d116 p := by
  change (if p 246 then d115 (change p 162 (some 163)) else d3 (change p 162 (some 163))) = d116 p
  rw [sub5277, sub5276]
  rfl
theorem sub5279 (p : Pattern) : d117 (change p 162 (some 163)) = d117 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d116 (change p 162 (some 163))) = d117 p
  rw [sub5140, sub5278]
  rfl
end NetHack.Sokoban22Refined85
