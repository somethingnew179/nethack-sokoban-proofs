/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub120 (p : Pattern) : d121 (change p 10000 none) = d121 p := by
  change (if p 204 then d12 (change p 10000 none) else d120 (change p 10000 none)) = d121 p
  rw [sub1, sub119]
  rfl
theorem sub121 (p : Pattern) : d122 (change p 10000 none) = d122 p := by
  change (if p 182 then d121 (change p 10000 none) else d103 (change p 10000 none)) = d122 p
  rw [sub120, sub99]
  rfl
theorem sub122 (p : Pattern) : d123 (change p 10000 none) = d123 p := by
  change (if p 163 then d122 (change p 10000 none) else d118 (change p 10000 none)) = d123 p
  rw [sub121, sub116]
  rfl
theorem sub123 (p : Pattern) : d124 (change p 10000 none) = d124 p := by
  change (if p 182 then d12 (change p 10000 none) else d103 (change p 10000 none)) = d124 p
  rw [sub1, sub99]
  rfl
theorem sub124 (p : Pattern) : d125 (change p 10000 none) = d125 p := by
  change (if p 182 then d12 (change p 10000 none) else d107 (change p 10000 none)) = d125 p
  rw [sub1, sub104]
  rfl
theorem sub125 (p : Pattern) : d126 (change p 10000 none) = d126 p := by
  change (if p 163 then d125 (change p 10000 none) else d124 (change p 10000 none)) = d126 p
  rw [sub124, sub123]
  rfl
theorem sub126 (p : Pattern) : d127 (change p 10000 none) = d127 p := by
  change (if p 162 then d126 (change p 10000 none) else d123 (change p 10000 none)) = d127 p
  rw [sub125, sub122]
  rfl
theorem sub127 (p : Pattern) : d128 (change p 10000 none) = d128 p := by
  change (if p 163 then d12 (change p 10000 none) else d70 (change p 10000 none)) = d128 p
  rw [sub1, sub65]
  rfl
theorem sub128 (p : Pattern) : d129 (change p 10000 none) = d129 p := by
  change (if p 162 then d128 (change p 10000 none) else d126 (change p 10000 none)) = d129 p
  rw [sub127, sub125]
  rfl
theorem sub129 (p : Pattern) : d130 (change p 10000 none) = d130 p := by
  change (if p 161 then d129 (change p 10000 none) else d127 (change p 10000 none)) = d130 p
  rw [sub128, sub126]
  rfl
theorem sub130 (p : Pattern) : d131 (change p 10000 none) = d131 p := by
  change (if p 160 then d130 (change p 10000 none) else d114 (change p 10000 none)) = d131 p
  rw [sub129, sub111]
  rfl
theorem sub131 (p : Pattern) : d132 (change p 10000 none) = d132 p := by
  change (if p 182 then d117 (change p 10000 none) else d116 (change p 10000 none)) = d132 p
  rw [sub115, sub114]
  rfl
theorem sub132 (p : Pattern) : d133 (change p 10000 none) = d133 p := by
  change (if p 163 then d132 (change p 10000 none) else d105 (change p 10000 none)) = d133 p
  rw [sub131, sub101]
  rfl
theorem sub133 (p : Pattern) : d134 (change p 10000 none) = d134 p := by
  change (if p 163 then d60 (change p 10000 none) else d109 (change p 10000 none)) = d134 p
  rw [sub55, sub106]
  rfl
theorem sub134 (p : Pattern) : d135 (change p 10000 none) = d135 p := by
  change (if p 162 then d134 (change p 10000 none) else d133 (change p 10000 none)) = d135 p
  rw [sub133, sub132]
  rfl
theorem sub135 (p : Pattern) : d136 (change p 10000 none) = d136 p := by
  change (if p 163 then d62 (change p 10000 none) else d109 (change p 10000 none)) = d136 p
  rw [sub57, sub106]
  rfl
theorem sub136 (p : Pattern) : d137 (change p 10000 none) = d137 p := by
  change (if p 162 then d12 (change p 10000 none) else d136 (change p 10000 none)) = d137 p
  rw [sub1, sub135]
  rfl
theorem sub137 (p : Pattern) : d138 (change p 10000 none) = d138 p := by
  change (if p 161 then d137 (change p 10000 none) else d135 (change p 10000 none)) = d138 p
  rw [sub136, sub134]
  rfl
theorem sub138 (p : Pattern) : d139 (change p 10000 none) = d139 p := by
  change (if p 182 then d12 (change p 10000 none) else d116 (change p 10000 none)) = d139 p
  rw [sub1, sub114]
  rfl
theorem sub139 (p : Pattern) : d140 (change p 10000 none) = d140 p := by
  change (if p 163 then d139 (change p 10000 none) else d122 (change p 10000 none)) = d140 p
  rw [sub138, sub121]
  rfl
theorem sub140 (p : Pattern) : d141 (change p 10000 none) = d141 p := by
  change (if p 163 then d70 (change p 10000 none) else d125 (change p 10000 none)) = d141 p
  rw [sub65, sub124]
  rfl
theorem sub141 (p : Pattern) : d142 (change p 10000 none) = d142 p := by
  change (if p 162 then d141 (change p 10000 none) else d140 (change p 10000 none)) = d142 p
  rw [sub140, sub139]
  rfl
theorem sub142 (p : Pattern) : d143 (change p 10000 none) = d143 p := by
  change (if p 163 then d72 (change p 10000 none) else d125 (change p 10000 none)) = d143 p
  rw [sub67, sub124]
  rfl
theorem sub143 (p : Pattern) : d144 (change p 10000 none) = d144 p := by
  change (if p 162 then d12 (change p 10000 none) else d143 (change p 10000 none)) = d144 p
  rw [sub1, sub142]
  rfl
theorem sub144 (p : Pattern) : d145 (change p 10000 none) = d145 p := by
  change (if p 161 then d144 (change p 10000 none) else d142 (change p 10000 none)) = d145 p
  rw [sub143, sub141]
  rfl
theorem sub145 (p : Pattern) : d146 (change p 10000 none) = d146 p := by
  change (if p 160 then d145 (change p 10000 none) else d138 (change p 10000 none)) = d146 p
  rw [sub144, sub137]
  rfl
theorem sub146 (p : Pattern) : d147 (change p 10000 none) = d147 p := by
  change (if p 141 then d146 (change p 10000 none) else d131 (change p 10000 none)) = d147 p
  rw [sub145, sub130]
  rfl
theorem sub147 (p : Pattern) : d148 (change p 10000 none) = d148 p := by
  change (if p 182 then d121 (change p 10000 none) else d120 (change p 10000 none)) = d148 p
  rw [sub120, sub119]
  rfl
theorem sub148 (p : Pattern) : d149 (change p 10000 none) = d149 p := by
  change (if p 163 then d148 (change p 10000 none) else d132 (change p 10000 none)) = d149 p
  rw [sub147, sub131]
  rfl
theorem sub149 (p : Pattern) : d150 (change p 10000 none) = d150 p := by
  change (if p 162 then d12 (change p 10000 none) else d149 (change p 10000 none)) = d150 p
  rw [sub1, sub148]
  rfl
theorem sub150 (p : Pattern) : d151 (change p 10000 none) = d151 p := by
  change (if p 161 then d12 (change p 10000 none) else d150 (change p 10000 none)) = d151 p
  rw [sub1, sub149]
  rfl
theorem sub151 (p : Pattern) : d152 (change p 10000 none) = d152 p := by
  change (if p 160 then d151 (change p 10000 none) else d114 (change p 10000 none)) = d152 p
  rw [sub150, sub111]
  rfl
theorem sub152 (p : Pattern) : d153 (change p 10000 none) = d153 p := by
  change (if p 163 then d12 (change p 10000 none) else d148 (change p 10000 none)) = d153 p
  rw [sub1, sub147]
  rfl
theorem sub153 (p : Pattern) : d154 (change p 10000 none) = d154 p := by
  change (if p 162 then d12 (change p 10000 none) else d153 (change p 10000 none)) = d154 p
  rw [sub1, sub152]
  rfl
theorem sub154 (p : Pattern) : d155 (change p 10000 none) = d155 p := by
  change (if p 161 then d12 (change p 10000 none) else d154 (change p 10000 none)) = d155 p
  rw [sub1, sub153]
  rfl
theorem sub155 (p : Pattern) : d156 (change p 10000 none) = d156 p := by
  change (if p 160 then d155 (change p 10000 none) else d138 (change p 10000 none)) = d156 p
  rw [sub154, sub137]
  rfl
theorem sub156 (p : Pattern) : d157 (change p 10000 none) = d157 p := by
  change (if p 141 then d156 (change p 10000 none) else d152 (change p 10000 none)) = d157 p
  rw [sub155, sub151]
  rfl
theorem sub157 (p : Pattern) : d158 (change p 10000 none) = d158 p := by
  change (if p 138 then d157 (change p 10000 none) else d147 (change p 10000 none)) = d158 p
  rw [sub156, sub146]
  rfl
theorem sub158 (p : Pattern) : d159 (change p 10000 none) = d159 p := by
  change (if p 162 then d12 (change p 10000 none) else d112 (change p 10000 none)) = d159 p
  rw [sub1, sub109]
  rfl
theorem sub159 (p : Pattern) : d160 (change p 10000 none) = d160 p := by
  change (if p 161 then d12 (change p 10000 none) else d159 (change p 10000 none)) = d160 p
  rw [sub1, sub158]
  rfl
theorem sub160 (p : Pattern) : d161 (change p 10000 none) = d161 p := by
  change (if p 160 then d12 (change p 10000 none) else d160 (change p 10000 none)) = d161 p
  rw [sub1, sub159]
  rfl
theorem sub161 (p : Pattern) : d162 (change p 10000 none) = d162 p := by
  change (if p 141 then d12 (change p 10000 none) else d161 (change p 10000 none)) = d162 p
  rw [sub1, sub160]
  rfl
theorem sub162 (p : Pattern) : d163 (change p 10000 none) = d163 p := by
  change (if p 138 then d162 (change p 10000 none) else d157 (change p 10000 none)) = d163 p
  rw [sub161, sub156]
  rfl
theorem sub163 (p : Pattern) : d164 (change p 10000 none) = d164 p := by
  change (if p 116 then d163 (change p 10000 none) else d158 (change p 10000 none)) = d164 p
  rw [sub162, sub157]
  rfl
theorem sub164 (p : Pattern) : d165 (change p 10000 none) = d165 p := by
  change (if p 138 then d12 (change p 10000 none) else d157 (change p 10000 none)) = d165 p
  rw [sub1, sub156]
  rfl
theorem sub165 (p : Pattern) : d166 (change p 10000 none) = d166 p := by
  change (if p 116 then d165 (change p 10000 none) else d158 (change p 10000 none)) = d166 p
  rw [sub164, sub157]
  rfl
theorem sub166 (p : Pattern) : d167 (change p 10000 none) = d167 p := by
  change (if p 115 then d166 (change p 10000 none) else d164 (change p 10000 none)) = d167 p
  rw [sub165, sub163]
  rfl
theorem sub167 (p : Pattern) : d168 (change p 10000 none) = d168 p := by
  change (if p 71 then d167 (change p 10000 none) else d101 (change p 10000 none)) = d168 p
  rw [sub166, sub96]
  rfl
theorem sub168 (p : Pattern) : d169 (change p 10000 none) = d169 p := by
  change (if p 49 then d168 (change p 10000 none) else d101 (change p 10000 none)) = d169 p
  rw [sub167, sub96]
  rfl
theorem sub169 (p : Pattern) : d170 (change p 10000 none) = d170 p := by
  change (if p 182 then d36 (change p 10000 none) else d31 (change p 10000 none)) = d170 p
  rw [sub29, sub23]
  rfl
theorem sub170 (p : Pattern) : d171 (change p 10000 none) = d171 p := by
  change (if p 163 then d170 (change p 10000 none) else d53 (change p 10000 none)) = d171 p
  rw [sub169, sub47]
  rfl
theorem sub171 (p : Pattern) : d172 (change p 10000 none) = d172 p := by
  change (if p 182 then d41 (change p 10000 none) else d31 (change p 10000 none)) = d172 p
  rw [sub35, sub23]
  rfl
theorem sub172 (p : Pattern) : d173 (change p 10000 none) = d173 p := by
  change (if p 182 then d12 (change p 10000 none) else d35 (change p 10000 none)) = d173 p
  rw [sub1, sub28]
  rfl
theorem sub173 (p : Pattern) : d174 (change p 10000 none) = d174 p := by
  change (if p 163 then d173 (change p 10000 none) else d172 (change p 10000 none)) = d174 p
  rw [sub172, sub171]
  rfl
theorem sub174 (p : Pattern) : d175 (change p 10000 none) = d175 p := by
  change (if p 162 then d174 (change p 10000 none) else d171 (change p 10000 none)) = d175 p
  rw [sub173, sub170]
  rfl
theorem sub175 (p : Pattern) : d176 (change p 10000 none) = d176 p := by
  change (if p 163 then d173 (change p 10000 none) else d66 (change p 10000 none)) = d176 p
  rw [sub172, sub61]
  rfl
theorem sub176 (p : Pattern) : d177 (change p 10000 none) = d177 p := by
  change (if p 162 then d73 (change p 10000 none) else d176 (change p 10000 none)) = d177 p
  rw [sub68, sub175]
  rfl
theorem sub177 (p : Pattern) : d178 (change p 10000 none) = d178 p := by
  change (if p 161 then d177 (change p 10000 none) else d175 (change p 10000 none)) = d178 p
  rw [sub176, sub174]
  rfl
theorem sub178 (p : Pattern) : d179 (change p 10000 none) = d179 p := by
  change (if p 160 then d178 (change p 10000 none) else d29 (change p 10000 none)) = d179 p
  rw [sub177, sub20]
  rfl
theorem sub179 (p : Pattern) : d180 (change p 10000 none) = d180 p := by
  change (if p 163 then d43 (change p 10000 none) else d170 (change p 10000 none)) = d180 p
  rw [sub37, sub169]
  rfl
theorem sub180 (p : Pattern) : d181 (change p 10000 none) = d181 p := by
  change (if p 163 then d72 (change p 10000 none) else d173 (change p 10000 none)) = d181 p
  rw [sub67, sub172]
  rfl
theorem sub181 (p : Pattern) : d182 (change p 10000 none) = d182 p := by
  change (if p 162 then d181 (change p 10000 none) else d180 (change p 10000 none)) = d182 p
  rw [sub180, sub179]
  rfl
theorem sub182 (p : Pattern) : d183 (change p 10000 none) = d183 p := by
  change (if p 163 then d12 (change p 10000 none) else d173 (change p 10000 none)) = d183 p
  rw [sub1, sub172]
  rfl
theorem sub183 (p : Pattern) : d184 (change p 10000 none) = d184 p := by
  change (if p 162 then d12 (change p 10000 none) else d183 (change p 10000 none)) = d184 p
  rw [sub1, sub182]
  rfl
theorem sub184 (p : Pattern) : d185 (change p 10000 none) = d185 p := by
  change (if p 161 then d184 (change p 10000 none) else d182 (change p 10000 none)) = d185 p
  rw [sub183, sub181]
  rfl
theorem sub185 (p : Pattern) : d186 (change p 10000 none) = d186 p := by
  change (if p 160 then d185 (change p 10000 none) else d65 (change p 10000 none)) = d186 p
  rw [sub184, sub60]
  rfl
theorem sub186 (p : Pattern) : d187 (change p 10000 none) = d187 p := by
  change (if p 141 then d186 (change p 10000 none) else d179 (change p 10000 none)) = d187 p
  rw [sub185, sub178]
  rfl
theorem sub187 (p : Pattern) : d188 (change p 10000 none) = d188 p := by
  change (if p 162 then d79 (change p 10000 none) else d16 (change p 10000 none)) = d188 p
  rw [sub74, sub5]
  rfl
theorem sub188 (p : Pattern) : d189 (change p 10000 none) = d189 p := by
  change (if p 161 then d80 (change p 10000 none) else d188 (change p 10000 none)) = d189 p
  rw [sub75, sub187]
  rfl
theorem sub189 (p : Pattern) : d8 (change p 10000 none) = d8 p := by
  rfl
theorem sub190 (p : Pattern) : d190 (change p 10000 none) = d190 p := by
  change (if p 247 then d12 (change p 10000 none) else d8 (change p 10000 none)) = d190 p
  rw [sub1, sub189]
  rfl
theorem sub191 (p : Pattern) : d191 (change p 10000 none) = d191 p := by
  change (if p 246 then d190 (change p 10000 none) else d8 (change p 10000 none)) = d191 p
  rw [sub190, sub189]
  rfl
theorem sub192 (p : Pattern) : d192 (change p 10000 none) = d192 p := by
  change (if p 204 then d12 (change p 10000 none) else d191 (change p 10000 none)) = d192 p
  rw [sub1, sub191]
  rfl
theorem sub193 (p : Pattern) : d193 (change p 10000 none) = d193 p := by
  change (if p 182 then d192 (change p 10000 none) else d191 (change p 10000 none)) = d193 p
  rw [sub192, sub191]
  rfl
theorem sub194 (p : Pattern) : d194 (change p 10000 none) = d194 p := by
  change (if p 163 then d193 (change p 10000 none) else d20 (change p 10000 none)) = d194 p
  rw [sub193, sub10]
  rfl
theorem sub195 (p : Pattern) : d195 (change p 10000 none) = d195 p := by
  change (if p 162 then d12 (change p 10000 none) else d194 (change p 10000 none)) = d195 p
  rw [sub1, sub194]
  rfl
theorem sub196 (p : Pattern) : d196 (change p 10000 none) = d196 p := by
  change (if p 161 then d12 (change p 10000 none) else d195 (change p 10000 none)) = d196 p
  rw [sub1, sub195]
  rfl
theorem sub197 (p : Pattern) : d197 (change p 10000 none) = d197 p := by
  change (if p 160 then d196 (change p 10000 none) else d189 (change p 10000 none)) = d197 p
  rw [sub196, sub188]
  rfl
theorem sub198 (p : Pattern) : d198 (change p 10000 none) = d198 p := by
  change (if p 163 then d62 (change p 10000 none) else d20 (change p 10000 none)) = d198 p
  rw [sub57, sub10]
  rfl
theorem sub199 (p : Pattern) : d199 (change p 10000 none) = d199 p := by
  change (if p 162 then d198 (change p 10000 none) else d53 (change p 10000 none)) = d199 p
  rw [sub198, sub47]
  rfl
theorem sub200 (p : Pattern) : d200 (change p 10000 none) = d200 p := by
  change (if p 161 then d84 (change p 10000 none) else d199 (change p 10000 none)) = d200 p
  rw [sub79, sub199]
  rfl
theorem sub201 (p : Pattern) : d201 (change p 10000 none) = d201 p := by
  change (if p 163 then d12 (change p 10000 none) else d193 (change p 10000 none)) = d201 p
  rw [sub1, sub193]
  rfl
theorem sub202 (p : Pattern) : d202 (change p 10000 none) = d202 p := by
  change (if p 162 then d12 (change p 10000 none) else d201 (change p 10000 none)) = d202 p
  rw [sub1, sub201]
  rfl
theorem sub203 (p : Pattern) : d203 (change p 10000 none) = d203 p := by
  change (if p 161 then d12 (change p 10000 none) else d202 (change p 10000 none)) = d203 p
  rw [sub1, sub202]
  rfl
theorem sub204 (p : Pattern) : d204 (change p 10000 none) = d204 p := by
  change (if p 160 then d203 (change p 10000 none) else d200 (change p 10000 none)) = d204 p
  rw [sub203, sub200]
  rfl
theorem sub205 (p : Pattern) : d205 (change p 10000 none) = d205 p := by
  change (if p 141 then d204 (change p 10000 none) else d197 (change p 10000 none)) = d205 p
  rw [sub204, sub197]
  rfl
theorem sub206 (p : Pattern) : d206 (change p 10000 none) = d206 p := by
  change (if p 138 then d205 (change p 10000 none) else d187 (change p 10000 none)) = d206 p
  rw [sub205, sub186]
  rfl
theorem sub207 (p : Pattern) : d207 (change p 10000 none) = d207 p := by
  change (if p 138 then d12 (change p 10000 none) else d205 (change p 10000 none)) = d207 p
  rw [sub1, sub205]
  rfl
theorem sub208 (p : Pattern) : d208 (change p 10000 none) = d208 p := by
  change (if p 116 then d207 (change p 10000 none) else d206 (change p 10000 none)) = d208 p
  rw [sub207, sub206]
  rfl
theorem sub209 (p : Pattern) : d209 (change p 10000 none) = d209 p := by
  change (if p 115 then d208 (change p 10000 none) else d98 (change p 10000 none)) = d209 p
  rw [sub208, sub93]
  rfl
theorem sub210 (p : Pattern) : d210 (change p 10000 none) = d210 p := by
  change (if p 71 then d209 (change p 10000 none) else d101 (change p 10000 none)) = d210 p
  rw [sub209, sub96]
  rfl
theorem sub211 (p : Pattern) : d211 (change p 10000 none) = d211 p := by
  change (if p 163 then d12 (change p 10000 none) else d109 (change p 10000 none)) = d211 p
  rw [sub1, sub106]
  rfl
theorem sub212 (p : Pattern) : d212 (change p 10000 none) = d212 p := by
  change (if p 162 then d211 (change p 10000 none) else d133 (change p 10000 none)) = d212 p
  rw [sub211, sub132]
  rfl
theorem sub213 (p : Pattern) : d213 (change p 10000 none) = d213 p := by
  change (if p 162 then d12 (change p 10000 none) else d211 (change p 10000 none)) = d213 p
  rw [sub1, sub211]
  rfl
theorem sub214 (p : Pattern) : d214 (change p 10000 none) = d214 p := by
  change (if p 161 then d213 (change p 10000 none) else d212 (change p 10000 none)) = d214 p
  rw [sub213, sub212]
  rfl
theorem sub215 (p : Pattern) : d215 (change p 10000 none) = d215 p := by
  change (if p 163 then d12 (change p 10000 none) else d125 (change p 10000 none)) = d215 p
  rw [sub1, sub124]
  rfl
theorem sub216 (p : Pattern) : d216 (change p 10000 none) = d216 p := by
  change (if p 162 then d215 (change p 10000 none) else d140 (change p 10000 none)) = d216 p
  rw [sub215, sub139]
  rfl
theorem sub217 (p : Pattern) : d217 (change p 10000 none) = d217 p := by
  change (if p 162 then d12 (change p 10000 none) else d215 (change p 10000 none)) = d217 p
  rw [sub1, sub215]
  rfl
theorem sub218 (p : Pattern) : d218 (change p 10000 none) = d218 p := by
  change (if p 161 then d217 (change p 10000 none) else d216 (change p 10000 none)) = d218 p
  rw [sub217, sub216]
  rfl
theorem sub219 (p : Pattern) : d219 (change p 10000 none) = d219 p := by
  change (if p 160 then d218 (change p 10000 none) else d214 (change p 10000 none)) = d219 p
  rw [sub218, sub214]
  rfl
theorem sub220 (p : Pattern) : d220 (change p 10000 none) = d220 p := by
  change (if p 141 then d219 (change p 10000 none) else d131 (change p 10000 none)) = d220 p
  rw [sub219, sub130]
  rfl
theorem sub221 (p : Pattern) : d221 (change p 10000 none) = d221 p := by
  change (if p 160 then d155 (change p 10000 none) else d214 (change p 10000 none)) = d221 p
  rw [sub154, sub214]
  rfl
theorem sub222 (p : Pattern) : d222 (change p 10000 none) = d222 p := by
  change (if p 141 then d221 (change p 10000 none) else d152 (change p 10000 none)) = d222 p
  rw [sub221, sub151]
  rfl
theorem sub223 (p : Pattern) : d223 (change p 10000 none) = d223 p := by
  change (if p 138 then d222 (change p 10000 none) else d220 (change p 10000 none)) = d223 p
  rw [sub222, sub220]
  rfl
theorem sub224 (p : Pattern) : d224 (change p 10000 none) = d224 p := by
  change (if p 138 then d162 (change p 10000 none) else d222 (change p 10000 none)) = d224 p
  rw [sub161, sub222]
  rfl
theorem sub225 (p : Pattern) : d225 (change p 10000 none) = d225 p := by
  change (if p 116 then d224 (change p 10000 none) else d223 (change p 10000 none)) = d225 p
  rw [sub224, sub223]
  rfl
theorem sub226 (p : Pattern) : d226 (change p 10000 none) = d226 p := by
  change (if p 182 then d121 (change p 10000 none) else d116 (change p 10000 none)) = d226 p
  rw [sub120, sub114]
  rfl
theorem sub227 (p : Pattern) : d227 (change p 10000 none) = d227 p := by
  change (if p 163 then d226 (change p 10000 none) else d132 (change p 10000 none)) = d227 p
  rw [sub226, sub131]
  rfl
theorem sub228 (p : Pattern) : d228 (change p 10000 none) = d228 p := by
  change (if p 162 then d215 (change p 10000 none) else d227 (change p 10000 none)) = d228 p
  rw [sub215, sub227]
  rfl
theorem sub229 (p : Pattern) : d229 (change p 10000 none) = d229 p := by
  change (if p 182 then d12 (change p 10000 none) else d120 (change p 10000 none)) = d229 p
  rw [sub1, sub119]
  rfl
theorem sub230 (p : Pattern) : d230 (change p 10000 none) = d230 p := by
  change (if p 163 then d12 (change p 10000 none) else d229 (change p 10000 none)) = d230 p
  rw [sub1, sub229]
  rfl
theorem sub231 (p : Pattern) : d231 (change p 10000 none) = d231 p := by
  change (if p 162 then d12 (change p 10000 none) else d230 (change p 10000 none)) = d231 p
  rw [sub1, sub230]
  rfl
theorem sub232 (p : Pattern) : d232 (change p 10000 none) = d232 p := by
  change (if p 161 then d231 (change p 10000 none) else d228 (change p 10000 none)) = d232 p
  rw [sub231, sub228]
  rfl
theorem sub233 (p : Pattern) : d233 (change p 10000 none) = d233 p := by
  change (if p 160 then d232 (change p 10000 none) else d114 (change p 10000 none)) = d233 p
  rw [sub232, sub111]
  rfl
theorem sub234 (p : Pattern) : d234 (change p 10000 none) = d234 p := by
  change (if p 182 then d121 (change p 10000 none) else d107 (change p 10000 none)) = d234 p
  rw [sub120, sub104]
  rfl
theorem sub235 (p : Pattern) : d235 (change p 10000 none) = d235 p := by
  change (if p 163 then d125 (change p 10000 none) else d234 (change p 10000 none)) = d235 p
  rw [sub124, sub234]
  rfl
theorem sub236 (p : Pattern) : d236 (change p 10000 none) = d236 p := by
  change (if p 162 then d230 (change p 10000 none) else d235 (change p 10000 none)) = d236 p
  rw [sub230, sub235]
  rfl
theorem sub237 (p : Pattern) : d237 (change p 10000 none) = d237 p := by
  change (if p 162 then d12 (change p 10000 none) else d49 (change p 10000 none)) = d237 p
  rw [sub1, sub43]
  rfl
theorem sub238 (p : Pattern) : d238 (change p 10000 none) = d238 p := by
  change (if p 161 then d237 (change p 10000 none) else d236 (change p 10000 none)) = d238 p
  rw [sub237, sub236]
  rfl
theorem sub239 (p : Pattern) : d239 (change p 10000 none) = d239 p := by
  change (if p 160 then d238 (change p 10000 none) else d214 (change p 10000 none)) = d239 p
  rw [sub238, sub214]
  rfl
end NetHack.Sokoban22Refined85
