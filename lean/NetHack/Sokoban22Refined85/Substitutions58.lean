/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions57
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6960 (p : Pattern) : d135 (change p 10000 (some 182)) = d4240 p := by
  change (if p 162 then d134 (change p 10000 (some 182)) else d133 (change p 10000 (some 182))) = d4240 p
  rw [sub6959, sub6958]
  rfl
theorem sub6961 (p : Pattern) : d136 (change p 10000 (some 182)) = d4241 p := by
  change (if p 163 then d62 (change p 10000 (some 182)) else d109 (change p 10000 (some 182))) = d4241 p
  rw [sub6883, sub6932]
  rfl
theorem sub6962 (p : Pattern) : d137 (change p 10000 (some 182)) = d4242 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d136 (change p 10000 (some 182))) = d4242 p
  rw [sub6827, sub6961]
  rfl
theorem sub6963 (p : Pattern) : d138 (change p 10000 (some 182)) = d4243 p := by
  change (if p 161 then d137 (change p 10000 (some 182)) else d135 (change p 10000 (some 182))) = d4243 p
  rw [sub6962, sub6960]
  rfl
theorem sub6964 (p : Pattern) : d139 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6965 (p : Pattern) : d140 (change p 10000 (some 182)) = d4281 p := by
  change (if p 163 then d139 (change p 10000 (some 182)) else d122 (change p 10000 (some 182))) = d4281 p
  rw [sub6964, sub6947]
  rfl
theorem sub6966 (p : Pattern) : d141 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d70 (change p 10000 (some 182)) else d125 (change p 10000 (some 182))) = d12 p
  rw [sub6891, sub6950]
  simp only [ite_self]
theorem sub6967 (p : Pattern) : d142 (change p 10000 (some 182)) = d4282 p := by
  change (if p 162 then d141 (change p 10000 (some 182)) else d140 (change p 10000 (some 182))) = d4282 p
  rw [sub6966, sub6965]
  rfl
theorem sub6968 (p : Pattern) : d143 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d72 (change p 10000 (some 182)) else d125 (change p 10000 (some 182))) = d12 p
  rw [sub6893, sub6950]
  simp only [ite_self]
theorem sub6969 (p : Pattern) : d144 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d143 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6968]
  simp only [ite_self]
theorem sub6970 (p : Pattern) : d145 (change p 10000 (some 182)) = d4920 p := by
  change (if p 161 then d144 (change p 10000 (some 182)) else d142 (change p 10000 (some 182))) = d4920 p
  rw [sub6969, sub6967]
  rfl
theorem sub6971 (p : Pattern) : d146 (change p 10000 (some 182)) = d4921 p := by
  change (if p 160 then d145 (change p 10000 (some 182)) else d138 (change p 10000 (some 182))) = d4921 p
  rw [sub6970, sub6963]
  rfl
theorem sub6972 (p : Pattern) : d147 (change p 10000 (some 182)) = d4922 p := by
  change (if p 141 then d146 (change p 10000 (some 182)) else d131 (change p 10000 (some 182))) = d4922 p
  rw [sub6971, sub6956]
  rfl
theorem sub6973 (p : Pattern) : d148 (change p 10000 (some 182)) = d121 p := by
  change d121 (change p 10000 (some 182)) = d121 p
  exact sub6946 p
theorem sub6974 (p : Pattern) : d149 (change p 10000 (some 182)) = d4916 p := by
  change (if p 163 then d148 (change p 10000 (some 182)) else d132 (change p 10000 (some 182))) = d4916 p
  rw [sub6973, sub6957]
  rfl
theorem sub6975 (p : Pattern) : d150 (change p 10000 (some 182)) = d4917 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d149 (change p 10000 (some 182))) = d4917 p
  rw [sub6827, sub6974]
  rfl
theorem sub6976 (p : Pattern) : d151 (change p 10000 (some 182)) = d4918 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d150 (change p 10000 (some 182))) = d4918 p
  rw [sub6827, sub6975]
  rfl
theorem sub6977 (p : Pattern) : d152 (change p 10000 (some 182)) = d4919 p := by
  change (if p 160 then d151 (change p 10000 (some 182)) else d114 (change p 10000 (some 182))) = d4919 p
  rw [sub6976, sub6937]
  rfl
theorem sub6978 (p : Pattern) : d153 (change p 10000 (some 182)) = d4281 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d148 (change p 10000 (some 182))) = d4281 p
  rw [sub6827, sub6973]
  rfl
theorem sub6979 (p : Pattern) : d154 (change p 10000 (some 182)) = d4282 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d153 (change p 10000 (some 182))) = d4282 p
  rw [sub6827, sub6978]
  rfl
theorem sub6980 (p : Pattern) : d155 (change p 10000 (some 182)) = d4920 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d154 (change p 10000 (some 182))) = d4920 p
  rw [sub6827, sub6979]
  rfl
theorem sub6981 (p : Pattern) : d156 (change p 10000 (some 182)) = d4921 p := by
  change (if p 160 then d155 (change p 10000 (some 182)) else d138 (change p 10000 (some 182))) = d4921 p
  rw [sub6980, sub6963]
  rfl
theorem sub6982 (p : Pattern) : d157 (change p 10000 (some 182)) = d4922 p := by
  change (if p 141 then d156 (change p 10000 (some 182)) else d152 (change p 10000 (some 182))) = d4922 p
  rw [sub6981, sub6977]
  rfl
theorem sub6983 (p : Pattern) : d158 (change p 10000 (some 182)) = d4922 p := by
  change (if p 138 then d157 (change p 10000 (some 182)) else d147 (change p 10000 (some 182))) = d4922 p
  rw [sub6982, sub6972]
  simp only [ite_self]
theorem sub6984 (p : Pattern) : d159 (change p 10000 (some 182)) = d4245 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d112 (change p 10000 (some 182))) = d4245 p
  rw [sub6827, sub6935]
  rfl
theorem sub6985 (p : Pattern) : d160 (change p 10000 (some 182)) = d4246 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d159 (change p 10000 (some 182))) = d4246 p
  rw [sub6827, sub6984]
  rfl
theorem sub6986 (p : Pattern) : d161 (change p 10000 (some 182)) = d4923 p := by
  change (if p 160 then d12 (change p 10000 (some 182)) else d160 (change p 10000 (some 182))) = d4923 p
  rw [sub6827, sub6985]
  rfl
theorem sub6987 (p : Pattern) : d162 (change p 10000 (some 182)) = d4924 p := by
  change (if p 141 then d12 (change p 10000 (some 182)) else d161 (change p 10000 (some 182))) = d4924 p
  rw [sub6827, sub6986]
  rfl
theorem sub6988 (p : Pattern) : d163 (change p 10000 (some 182)) = d4925 p := by
  change (if p 138 then d162 (change p 10000 (some 182)) else d157 (change p 10000 (some 182))) = d4925 p
  rw [sub6987, sub6982]
  rfl
theorem sub6989 (p : Pattern) : d164 (change p 10000 (some 182)) = d4926 p := by
  change (if p 116 then d163 (change p 10000 (some 182)) else d158 (change p 10000 (some 182))) = d4926 p
  rw [sub6988, sub6983]
  rfl
theorem sub6990 (p : Pattern) : d165 (change p 10000 (some 182)) = d4927 p := by
  change (if p 138 then d12 (change p 10000 (some 182)) else d157 (change p 10000 (some 182))) = d4927 p
  rw [sub6827, sub6982]
  rfl
theorem sub6991 (p : Pattern) : d166 (change p 10000 (some 182)) = d4928 p := by
  change (if p 116 then d165 (change p 10000 (some 182)) else d158 (change p 10000 (some 182))) = d4928 p
  rw [sub6990, sub6983]
  rfl
theorem sub6992 (p : Pattern) : d167 (change p 10000 (some 182)) = d4929 p := by
  change (if p 115 then d166 (change p 10000 (some 182)) else d164 (change p 10000 (some 182))) = d4929 p
  rw [sub6991, sub6989]
  rfl
theorem sub6993 (p : Pattern) : d168 (change p 10000 (some 182)) = d4930 p := by
  change (if p 71 then d167 (change p 10000 (some 182)) else d101 (change p 10000 (some 182))) = d4930 p
  rw [sub6992, sub6922]
  rfl
theorem sub6994 (p : Pattern) : d169 (change p 10000 (some 182)) = d4931 p := by
  change (if p 49 then d168 (change p 10000 (some 182)) else d101 (change p 10000 (some 182))) = d4931 p
  rw [sub6993, sub6922]
  rfl
theorem sub6995 (p : Pattern) : d170 (change p 10000 (some 182)) = d36 p := by
  change d36 (change p 10000 (some 182)) = d36 p
  exact sub6855 p
theorem sub6996 (p : Pattern) : d171 (change p 10000 (some 182)) = d4255 p := by
  change (if p 163 then d170 (change p 10000 (some 182)) else d53 (change p 10000 (some 182))) = d4255 p
  rw [sub6995, sub6873]
  rfl
theorem sub6997 (p : Pattern) : d172 (change p 10000 (some 182)) = d41 p := by
  change d41 (change p 10000 (some 182)) = d41 p
  exact sub6861 p
theorem sub6998 (p : Pattern) : d173 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub6999 (p : Pattern) : d174 (change p 10000 (some 182)) = d4218 p := by
  change (if p 163 then d173 (change p 10000 (some 182)) else d172 (change p 10000 (some 182))) = d4218 p
  rw [sub6998, sub6997]
  rfl
theorem sub7000 (p : Pattern) : d175 (change p 10000 (some 182)) = d4257 p := by
  change (if p 162 then d174 (change p 10000 (some 182)) else d171 (change p 10000 (some 182))) = d4257 p
  rw [sub6999, sub6996]
  rfl
theorem sub7001 (p : Pattern) : d176 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d173 (change p 10000 (some 182)) else d66 (change p 10000 (some 182))) = d12 p
  rw [sub6998, sub6887]
  simp only [ite_self]
theorem sub7002 (p : Pattern) : d177 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d73 (change p 10000 (some 182)) else d176 (change p 10000 (some 182))) = d12 p
  rw [sub6894, sub7001]
  simp only [ite_self]
theorem sub7003 (p : Pattern) : d178 (change p 10000 (some 182)) = d4903 p := by
  change (if p 161 then d177 (change p 10000 (some 182)) else d175 (change p 10000 (some 182))) = d4903 p
  rw [sub7002, sub7000]
  rfl
theorem sub7004 (p : Pattern) : d179 (change p 10000 (some 182)) = d4904 p := by
  change (if p 160 then d178 (change p 10000 (some 182)) else d29 (change p 10000 (some 182))) = d4904 p
  rw [sub7003, sub6846]
  rfl
theorem sub7005 (p : Pattern) : d180 (change p 10000 (some 182)) = d4261 p := by
  change (if p 163 then d43 (change p 10000 (some 182)) else d170 (change p 10000 (some 182))) = d4261 p
  rw [sub6863, sub6995]
  rfl
theorem sub7006 (p : Pattern) : d181 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d72 (change p 10000 (some 182)) else d173 (change p 10000 (some 182))) = d12 p
  rw [sub6893, sub6998]
  simp only [ite_self]
theorem sub7007 (p : Pattern) : d182 (change p 10000 (some 182)) = d4262 p := by
  change (if p 162 then d181 (change p 10000 (some 182)) else d180 (change p 10000 (some 182))) = d4262 p
  rw [sub7006, sub7005]
  rfl
theorem sub7008 (p : Pattern) : d183 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d173 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6998]
  simp only [ite_self]
theorem sub7009 (p : Pattern) : d184 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d183 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub7008]
  simp only [ite_self]
theorem sub7010 (p : Pattern) : d185 (change p 10000 (some 182)) = d4905 p := by
  change (if p 161 then d184 (change p 10000 (some 182)) else d182 (change p 10000 (some 182))) = d4905 p
  rw [sub7009, sub7007]
  rfl
theorem sub7011 (p : Pattern) : d186 (change p 10000 (some 182)) = d4906 p := by
  change (if p 160 then d185 (change p 10000 (some 182)) else d65 (change p 10000 (some 182))) = d4906 p
  rw [sub7010, sub6886]
  rfl
theorem sub7012 (p : Pattern) : d187 (change p 10000 (some 182)) = d4907 p := by
  change (if p 141 then d186 (change p 10000 (some 182)) else d179 (change p 10000 (some 182))) = d4907 p
  rw [sub7011, sub7004]
  rfl
theorem sub7013 (p : Pattern) : d188 (change p 10000 (some 182)) = d4256 p := by
  change (if p 162 then d79 (change p 10000 (some 182)) else d16 (change p 10000 (some 182))) = d4256 p
  rw [sub6900, sub6831]
  rfl
theorem sub7014 (p : Pattern) : d189 (change p 10000 (some 182)) = d4258 p := by
  change (if p 161 then d80 (change p 10000 (some 182)) else d188 (change p 10000 (some 182))) = d4258 p
  rw [sub6901, sub7013]
  rfl
theorem sub7015 (p : Pattern) : d8 (change p 10000 (some 182)) = d8 p := by
  rfl
theorem sub7016 (p : Pattern) : d190 (change p 10000 (some 182)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 182)) else d8 (change p 10000 (some 182))) = d190 p
  rw [sub6827, sub7015]
  rfl
theorem sub7017 (p : Pattern) : d191 (change p 10000 (some 182)) = d191 p := by
  change (if p 246 then d190 (change p 10000 (some 182)) else d8 (change p 10000 (some 182))) = d191 p
  rw [sub7016, sub7015]
  rfl
theorem sub7018 (p : Pattern) : d192 (change p 10000 (some 182)) = d192 p := by
  change (if p 204 then d12 (change p 10000 (some 182)) else d191 (change p 10000 (some 182))) = d192 p
  rw [sub6827, sub7017]
  rfl
theorem sub7019 (p : Pattern) : d193 (change p 10000 (some 182)) = d192 p := by
  change d192 (change p 10000 (some 182)) = d192 p
  exact sub7018 p
theorem sub7020 (p : Pattern) : d194 (change p 10000 (some 182)) = d4932 p := by
  change (if p 163 then d193 (change p 10000 (some 182)) else d20 (change p 10000 (some 182))) = d4932 p
  rw [sub7019, sub6836]
  rfl
theorem sub7021 (p : Pattern) : d195 (change p 10000 (some 182)) = d4933 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d194 (change p 10000 (some 182))) = d4933 p
  rw [sub6827, sub7020]
  rfl
theorem sub7022 (p : Pattern) : d196 (change p 10000 (some 182)) = d4934 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d195 (change p 10000 (some 182))) = d4934 p
  rw [sub6827, sub7021]
  rfl
theorem sub7023 (p : Pattern) : d197 (change p 10000 (some 182)) = d4935 p := by
  change (if p 160 then d196 (change p 10000 (some 182)) else d189 (change p 10000 (some 182))) = d4935 p
  rw [sub7022, sub7014]
  rfl
theorem sub7024 (p : Pattern) : d198 (change p 10000 (some 182)) = d4259 p := by
  change (if p 163 then d62 (change p 10000 (some 182)) else d20 (change p 10000 (some 182))) = d4259 p
  rw [sub6883, sub6836]
  rfl
theorem sub7025 (p : Pattern) : d199 (change p 10000 (some 182)) = d4260 p := by
  change (if p 162 then d198 (change p 10000 (some 182)) else d53 (change p 10000 (some 182))) = d4260 p
  rw [sub7024, sub6873]
  rfl
theorem sub7026 (p : Pattern) : d200 (change p 10000 (some 182)) = d4263 p := by
  change (if p 161 then d84 (change p 10000 (some 182)) else d199 (change p 10000 (some 182))) = d4263 p
  rw [sub6905, sub7025]
  rfl
theorem sub7027 (p : Pattern) : d201 (change p 10000 (some 182)) = d4936 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d193 (change p 10000 (some 182))) = d4936 p
  rw [sub6827, sub7019]
  rfl
theorem sub7028 (p : Pattern) : d202 (change p 10000 (some 182)) = d4937 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d201 (change p 10000 (some 182))) = d4937 p
  rw [sub6827, sub7027]
  rfl
theorem sub7029 (p : Pattern) : d203 (change p 10000 (some 182)) = d4938 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d202 (change p 10000 (some 182))) = d4938 p
  rw [sub6827, sub7028]
  rfl
theorem sub7030 (p : Pattern) : d204 (change p 10000 (some 182)) = d4939 p := by
  change (if p 160 then d203 (change p 10000 (some 182)) else d200 (change p 10000 (some 182))) = d4939 p
  rw [sub7029, sub7026]
  rfl
theorem sub7031 (p : Pattern) : d205 (change p 10000 (some 182)) = d4940 p := by
  change (if p 141 then d204 (change p 10000 (some 182)) else d197 (change p 10000 (some 182))) = d4940 p
  rw [sub7030, sub7023]
  rfl
theorem sub7032 (p : Pattern) : d206 (change p 10000 (some 182)) = d4941 p := by
  change (if p 138 then d205 (change p 10000 (some 182)) else d187 (change p 10000 (some 182))) = d4941 p
  rw [sub7031, sub7012]
  rfl
theorem sub7033 (p : Pattern) : d207 (change p 10000 (some 182)) = d4942 p := by
  change (if p 138 then d12 (change p 10000 (some 182)) else d205 (change p 10000 (some 182))) = d4942 p
  rw [sub6827, sub7031]
  rfl
theorem sub7034 (p : Pattern) : d208 (change p 10000 (some 182)) = d4943 p := by
  change (if p 116 then d207 (change p 10000 (some 182)) else d206 (change p 10000 (some 182))) = d4943 p
  rw [sub7033, sub7032]
  rfl
theorem sub7035 (p : Pattern) : d209 (change p 10000 (some 182)) = d4944 p := by
  change (if p 115 then d208 (change p 10000 (some 182)) else d98 (change p 10000 (some 182))) = d4944 p
  rw [sub7034, sub6919]
  rfl
theorem sub7036 (p : Pattern) : d210 (change p 10000 (some 182)) = d4945 p := by
  change (if p 71 then d209 (change p 10000 (some 182)) else d101 (change p 10000 (some 182))) = d4945 p
  rw [sub7035, sub6922]
  rfl
theorem sub7037 (p : Pattern) : d211 (change p 10000 (some 182)) = d4270 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d109 (change p 10000 (some 182))) = d4270 p
  rw [sub6827, sub6932]
  rfl
theorem sub7038 (p : Pattern) : d212 (change p 10000 (some 182)) = d4271 p := by
  change (if p 162 then d211 (change p 10000 (some 182)) else d133 (change p 10000 (some 182))) = d4271 p
  rw [sub7037, sub6958]
  rfl
theorem sub7039 (p : Pattern) : d213 (change p 10000 (some 182)) = d4272 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d211 (change p 10000 (some 182))) = d4272 p
  rw [sub6827, sub7037]
  rfl
theorem sub7040 (p : Pattern) : d214 (change p 10000 (some 182)) = d4273 p := by
  change (if p 161 then d213 (change p 10000 (some 182)) else d212 (change p 10000 (some 182))) = d4273 p
  rw [sub7039, sub7038]
  rfl
theorem sub7041 (p : Pattern) : d215 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d125 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6950]
  simp only [ite_self]
theorem sub7042 (p : Pattern) : d216 (change p 10000 (some 182)) = d4282 p := by
  change (if p 162 then d215 (change p 10000 (some 182)) else d140 (change p 10000 (some 182))) = d4282 p
  rw [sub7041, sub6965]
  rfl
theorem sub7043 (p : Pattern) : d217 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d215 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub7041]
  simp only [ite_self]
theorem sub7044 (p : Pattern) : d218 (change p 10000 (some 182)) = d4920 p := by
  change (if p 161 then d217 (change p 10000 (some 182)) else d216 (change p 10000 (some 182))) = d4920 p
  rw [sub7043, sub7042]
  rfl
theorem sub7045 (p : Pattern) : d219 (change p 10000 (some 182)) = d4946 p := by
  change (if p 160 then d218 (change p 10000 (some 182)) else d214 (change p 10000 (some 182))) = d4946 p
  rw [sub7044, sub7040]
  rfl
theorem sub7046 (p : Pattern) : d220 (change p 10000 (some 182)) = d4947 p := by
  change (if p 141 then d219 (change p 10000 (some 182)) else d131 (change p 10000 (some 182))) = d4947 p
  rw [sub7045, sub6956]
  rfl
theorem sub7047 (p : Pattern) : d221 (change p 10000 (some 182)) = d4946 p := by
  change (if p 160 then d155 (change p 10000 (some 182)) else d214 (change p 10000 (some 182))) = d4946 p
  rw [sub6980, sub7040]
  rfl
theorem sub7048 (p : Pattern) : d222 (change p 10000 (some 182)) = d4947 p := by
  change (if p 141 then d221 (change p 10000 (some 182)) else d152 (change p 10000 (some 182))) = d4947 p
  rw [sub7047, sub6977]
  rfl
theorem sub7049 (p : Pattern) : d223 (change p 10000 (some 182)) = d4947 p := by
  change (if p 138 then d222 (change p 10000 (some 182)) else d220 (change p 10000 (some 182))) = d4947 p
  rw [sub7048, sub7046]
  simp only [ite_self]
theorem sub7050 (p : Pattern) : d224 (change p 10000 (some 182)) = d4948 p := by
  change (if p 138 then d162 (change p 10000 (some 182)) else d222 (change p 10000 (some 182))) = d4948 p
  rw [sub6987, sub7048]
  rfl
theorem sub7051 (p : Pattern) : d225 (change p 10000 (some 182)) = d4949 p := by
  change (if p 116 then d224 (change p 10000 (some 182)) else d223 (change p 10000 (some 182))) = d4949 p
  rw [sub7050, sub7049]
  rfl
theorem sub7052 (p : Pattern) : d226 (change p 10000 (some 182)) = d121 p := by
  change d121 (change p 10000 (some 182)) = d121 p
  exact sub6946 p
theorem sub7053 (p : Pattern) : d227 (change p 10000 (some 182)) = d4916 p := by
  change (if p 163 then d226 (change p 10000 (some 182)) else d132 (change p 10000 (some 182))) = d4916 p
  rw [sub7052, sub6957]
  rfl
theorem sub7054 (p : Pattern) : d228 (change p 10000 (some 182)) = d4917 p := by
  change (if p 162 then d215 (change p 10000 (some 182)) else d227 (change p 10000 (some 182))) = d4917 p
  rw [sub7041, sub7053]
  rfl
theorem sub7055 (p : Pattern) : d229 (change p 10000 (some 182)) = d12 p := by
  change d12 (change p 10000 (some 182)) = d12 p
  exact sub6827 p
theorem sub7056 (p : Pattern) : d230 (change p 10000 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 10000 (some 182)) else d229 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub7055]
  simp only [ite_self]
theorem sub7057 (p : Pattern) : d231 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d230 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub7056]
  simp only [ite_self]
theorem sub7058 (p : Pattern) : d232 (change p 10000 (some 182)) = d4918 p := by
  change (if p 161 then d231 (change p 10000 (some 182)) else d228 (change p 10000 (some 182))) = d4918 p
  rw [sub7057, sub7054]
  rfl
theorem sub7059 (p : Pattern) : d233 (change p 10000 (some 182)) = d4919 p := by
  change (if p 160 then d232 (change p 10000 (some 182)) else d114 (change p 10000 (some 182))) = d4919 p
  rw [sub7058, sub6937]
  rfl
theorem sub7060 (p : Pattern) : d234 (change p 10000 (some 182)) = d121 p := by
  change d121 (change p 10000 (some 182)) = d121 p
  exact sub6946 p
theorem sub7061 (p : Pattern) : d235 (change p 10000 (some 182)) = d4281 p := by
  change (if p 163 then d125 (change p 10000 (some 182)) else d234 (change p 10000 (some 182))) = d4281 p
  rw [sub6950, sub7060]
  rfl
theorem sub7062 (p : Pattern) : d236 (change p 10000 (some 182)) = d4282 p := by
  change (if p 162 then d230 (change p 10000 (some 182)) else d235 (change p 10000 (some 182))) = d4282 p
  rw [sub7056, sub7061]
  rfl
theorem sub7063 (p : Pattern) : d237 (change p 10000 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d49 (change p 10000 (some 182))) = d12 p
  rw [sub6827, sub6869]
  simp only [ite_self]
theorem sub7064 (p : Pattern) : d238 (change p 10000 (some 182)) = d4920 p := by
  change (if p 161 then d237 (change p 10000 (some 182)) else d236 (change p 10000 (some 182))) = d4920 p
  rw [sub7063, sub7062]
  rfl
theorem sub7065 (p : Pattern) : d239 (change p 10000 (some 182)) = d4946 p := by
  change (if p 160 then d238 (change p 10000 (some 182)) else d214 (change p 10000 (some 182))) = d4946 p
  rw [sub7064, sub7040]
  rfl
theorem sub7066 (p : Pattern) : d240 (change p 10000 (some 182)) = d4947 p := by
  change (if p 141 then d239 (change p 10000 (some 182)) else d233 (change p 10000 (some 182))) = d4947 p
  rw [sub7065, sub7059]
  rfl
theorem sub7067 (p : Pattern) : d241 (change p 10000 (some 182)) = d4277 p := by
  change (if p 163 then d62 (change p 10000 (some 182)) else d132 (change p 10000 (some 182))) = d4277 p
  rw [sub6883, sub6957]
  rfl
theorem sub7068 (p : Pattern) : d242 (change p 10000 (some 182)) = d4278 p := by
  change (if p 162 then d241 (change p 10000 (some 182)) else d105 (change p 10000 (some 182))) = d4278 p
  rw [sub7067, sub6927]
  rfl
theorem sub7069 (p : Pattern) : d243 (change p 10000 (some 182)) = d4279 p := by
  change (if p 161 then d137 (change p 10000 (some 182)) else d242 (change p 10000 (some 182))) = d4279 p
  rw [sub6962, sub7068]
  rfl
theorem sub7070 (p : Pattern) : d244 (change p 10000 (some 182)) = d4950 p := by
  change (if p 160 then d155 (change p 10000 (some 182)) else d243 (change p 10000 (some 182))) = d4950 p
  rw [sub6980, sub7069]
  rfl
theorem sub7071 (p : Pattern) : d245 (change p 10000 (some 182)) = d4280 p := by
  change (if p 162 then d211 (change p 10000 (some 182)) else d132 (change p 10000 (some 182))) = d4280 p
  rw [sub7037, sub6957]
  rfl
theorem sub7072 (p : Pattern) : d246 (change p 10000 (some 182)) = d4283 p := by
  change (if p 161 then d154 (change p 10000 (some 182)) else d245 (change p 10000 (some 182))) = d4283 p
  rw [sub6979, sub7071]
  rfl
theorem sub7073 (p : Pattern) : d247 (change p 10000 (some 182)) = d4951 p := by
  change (if p 162 then d12 (change p 10000 (some 182)) else d27 (change p 10000 (some 182))) = d4951 p
  rw [sub6827, sub6844]
  rfl
theorem sub7074 (p : Pattern) : d248 (change p 10000 (some 182)) = d4952 p := by
  change (if p 161 then d12 (change p 10000 (some 182)) else d247 (change p 10000 (some 182))) = d4952 p
  rw [sub6827, sub7073]
  rfl
theorem sub7075 (p : Pattern) : d249 (change p 10000 (some 182)) = d4953 p := by
  change (if p 160 then d248 (change p 10000 (some 182)) else d246 (change p 10000 (some 182))) = d4953 p
  rw [sub7074, sub7072]
  rfl
theorem sub7076 (p : Pattern) : d250 (change p 10000 (some 182)) = d4954 p := by
  change (if p 141 then d249 (change p 10000 (some 182)) else d244 (change p 10000 (some 182))) = d4954 p
  rw [sub7075, sub7070]
  rfl
theorem sub7077 (p : Pattern) : d251 (change p 10000 (some 182)) = d4955 p := by
  change (if p 138 then d250 (change p 10000 (some 182)) else d240 (change p 10000 (some 182))) = d4955 p
  rw [sub7076, sub7066]
  rfl
theorem sub7078 (p : Pattern) : d252 (change p 10000 (some 182)) = d4286 p := by
  change (if p 163 then d26 (change p 10000 (some 182)) else d132 (change p 10000 (some 182))) = d4286 p
  rw [sub6843, sub6957]
  rfl
theorem sub7079 (p : Pattern) : d253 (change p 10000 (some 182)) = d4287 p := by
  change (if p 162 then d252 (change p 10000 (some 182)) else d105 (change p 10000 (some 182))) = d4287 p
  rw [sub7078, sub6927]
  rfl
end NetHack.Sokoban22Refined85
