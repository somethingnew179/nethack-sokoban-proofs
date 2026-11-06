/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub120 (p : Pattern) : d160 (change p 10000 none) = d160 p := by
  change (if p 132 then d159 (change p 10000 none) else d152 (change p 10000 none)) = d160 p
  rw [sub119, sub112]
  rfl
theorem sub121 (p : Pattern) : d161 (change p 10000 none) = d161 p := by
  change (if p 108 then d160 (change p 10000 none) else d136 (change p 10000 none)) = d161 p
  rw [sub120, sub96]
  rfl
theorem sub122 (p : Pattern) : d0 (change p 132 (some 158)) = d0 p := by
  rfl
theorem sub123 (p : Pattern) : d2 (change p 132 (some 158)) = d2 p := by
  rfl
theorem sub124 (p : Pattern) : d6 (change p 132 (some 158)) = d6 p := by
  change (if p 193 then d2 (change p 132 (some 158)) else d0 (change p 132 (some 158))) = d6 p
  rw [sub123, sub122]
  rfl
theorem sub125 (p : Pattern) : d7 (change p 132 (some 158)) = d7 p := by
  change (if p 192 then d6 (change p 132 (some 158)) else d0 (change p 132 (some 158))) = d7 p
  rw [sub124, sub122]
  rfl
theorem sub126 (p : Pattern) : d4 (change p 132 (some 158)) = d4 p := by
  rfl
theorem sub127 (p : Pattern) : d54 (change p 132 (some 158)) = d54 p := by
  change (if p 193 then d4 (change p 132 (some 158)) else d2 (change p 132 (some 158))) = d54 p
  rw [sub126, sub123]
  rfl
theorem sub128 (p : Pattern) : d55 (change p 132 (some 158)) = d55 p := by
  change (if p 192 then d54 (change p 132 (some 158)) else d2 (change p 132 (some 158))) = d55 p
  rw [sub127, sub123]
  rfl
theorem sub129 (p : Pattern) : d56 (change p 132 (some 158)) = d56 p := by
  change (if p 186 then d55 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d56 p
  rw [sub128, sub125]
  rfl
theorem sub130 (p : Pattern) : d57 (change p 132 (some 158)) = d57 p := by
  change (if p 160 then d56 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d57 p
  rw [sub129, sub125]
  rfl
theorem sub131 (p : Pattern) : d1 (change p 132 (some 158)) = d1 p := by
  rfl
theorem sub132 (p : Pattern) : d8 (change p 132 (some 158)) = d8 p := by
  change (if p 271 then d1 (change p 132 (some 158)) else d0 (change p 132 (some 158))) = d8 p
  rw [sub131, sub122]
  rfl
theorem sub133 (p : Pattern) : d3 (change p 132 (some 158)) = d3 p := by
  rfl
theorem sub134 (p : Pattern) : d9 (change p 132 (some 158)) = d9 p := by
  change (if p 271 then d3 (change p 132 (some 158)) else d2 (change p 132 (some 158))) = d9 p
  rw [sub133, sub123]
  rfl
theorem sub135 (p : Pattern) : d10 (change p 132 (some 158)) = d10 p := by
  change (if p 193 then d9 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d10 p
  rw [sub134, sub132]
  rfl
theorem sub136 (p : Pattern) : d11 (change p 132 (some 158)) = d11 p := by
  change (if p 192 then d10 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d11 p
  rw [sub135, sub132]
  rfl
theorem sub137 (p : Pattern) : d12 (change p 132 (some 158)) = d12 p := by
  change (if p 168 then d11 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d12 p
  rw [sub136, sub125]
  rfl
theorem sub138 (p : Pattern) : d5 (change p 132 (some 158)) = d5 p := by
  rfl
theorem sub139 (p : Pattern) : d58 (change p 132 (some 158)) = d58 p := by
  change (if p 271 then d5 (change p 132 (some 158)) else d4 (change p 132 (some 158))) = d58 p
  rw [sub138, sub126]
  rfl
theorem sub140 (p : Pattern) : d59 (change p 132 (some 158)) = d59 p := by
  change (if p 193 then d58 (change p 132 (some 158)) else d9 (change p 132 (some 158))) = d59 p
  rw [sub139, sub134]
  rfl
theorem sub141 (p : Pattern) : d60 (change p 132 (some 158)) = d60 p := by
  change (if p 192 then d59 (change p 132 (some 158)) else d9 (change p 132 (some 158))) = d60 p
  rw [sub140, sub134]
  rfl
theorem sub142 (p : Pattern) : d61 (change p 132 (some 158)) = d61 p := by
  change (if p 186 then d60 (change p 132 (some 158)) else d11 (change p 132 (some 158))) = d61 p
  rw [sub141, sub136]
  rfl
theorem sub143 (p : Pattern) : d62 (change p 132 (some 158)) = d62 p := by
  change (if p 168 then d61 (change p 132 (some 158)) else d56 (change p 132 (some 158))) = d62 p
  rw [sub142, sub129]
  rfl
theorem sub144 (p : Pattern) : d63 (change p 132 (some 158)) = d63 p := by
  change (if p 160 then d62 (change p 132 (some 158)) else d12 (change p 132 (some 158))) = d63 p
  rw [sub143, sub137]
  rfl
theorem sub145 (p : Pattern) : d64 (change p 132 (some 158)) = d64 p := by
  change (if p 141 then d63 (change p 132 (some 158)) else d57 (change p 132 (some 158))) = d64 p
  rw [sub144, sub130]
  rfl
theorem sub146 (p : Pattern) : d106 (change p 132 (some 158)) = d106 p := by
  change (if p 160 then d55 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d106 p
  rw [sub128, sub125]
  rfl
theorem sub147 (p : Pattern) : d107 (change p 132 (some 158)) = d107 p := by
  change (if p 159 then d55 (change p 132 (some 158)) else d106 (change p 132 (some 158))) = d107 p
  rw [sub128, sub146]
  rfl
theorem sub148 (p : Pattern) : d108 (change p 132 (some 158)) = d107 p := by
  change d107 (change p 132 (some 158)) = d107 p
  exact sub147 p
theorem sub149 (p : Pattern) : d65 (change p 132 (some 158)) = d65 p := by
  change (if p 168 then d60 (change p 132 (some 158)) else d55 (change p 132 (some 158))) = d65 p
  rw [sub141, sub128]
  rfl
theorem sub150 (p : Pattern) : d109 (change p 132 (some 158)) = d109 p := by
  change (if p 160 then d65 (change p 132 (some 158)) else d12 (change p 132 (some 158))) = d109 p
  rw [sub149, sub137]
  rfl
theorem sub151 (p : Pattern) : d110 (change p 132 (some 158)) = d110 p := by
  change (if p 159 then d65 (change p 132 (some 158)) else d109 (change p 132 (some 158))) = d110 p
  rw [sub149, sub150]
  rfl
theorem sub152 (p : Pattern) : d111 (change p 132 (some 158)) = d110 p := by
  change d110 (change p 132 (some 158)) = d110 p
  exact sub151 p
theorem sub153 (p : Pattern) : d112 (change p 132 (some 158)) = d336 p := by
  change (if p 141 then d111 (change p 132 (some 158)) else d108 (change p 132 (some 158))) = d336 p
  rw [sub152, sub148]
  rfl
theorem sub154 (p : Pattern) : d113 (change p 132 (some 158)) = d744 p := by
  change (if p 134 then d112 (change p 132 (some 158)) else d64 (change p 132 (some 158))) = d744 p
  rw [sub153, sub145]
  rfl
theorem sub155 (p : Pattern) : d114 (change p 132 (some 158)) = d114 p := by
  change (if p 159 then d55 (change p 132 (some 158)) else d57 (change p 132 (some 158))) = d114 p
  rw [sub128, sub130]
  rfl
theorem sub156 (p : Pattern) : d115 (change p 132 (some 158)) = d114 p := by
  change d114 (change p 132 (some 158)) = d114 p
  exact sub155 p
theorem sub157 (p : Pattern) : d116 (change p 132 (some 158)) = d116 p := by
  change (if p 159 then d65 (change p 132 (some 158)) else d63 (change p 132 (some 158))) = d116 p
  rw [sub149, sub144]
  rfl
theorem sub158 (p : Pattern) : d117 (change p 132 (some 158)) = d116 p := by
  change d116 (change p 132 (some 158)) = d116 p
  exact sub157 p
theorem sub159 (p : Pattern) : d118 (change p 132 (some 158)) = d335 p := by
  change (if p 141 then d117 (change p 132 (some 158)) else d115 (change p 132 (some 158))) = d335 p
  rw [sub158, sub156]
  rfl
theorem sub160 (p : Pattern) : d119 (change p 132 (some 158)) = d119 p := by
  change (if p 187 then d55 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d119 p
  rw [sub128, sub125]
  rfl
theorem sub161 (p : Pattern) : d120 (change p 132 (some 158)) = d120 p := by
  change (if p 186 then d119 (change p 132 (some 158)) else d7 (change p 132 (some 158))) = d120 p
  rw [sub160, sub125]
  rfl
theorem sub162 (p : Pattern) : d121 (change p 132 (some 158)) = d121 p := by
  change (if p 160 then d55 (change p 132 (some 158)) else d120 (change p 132 (some 158))) = d121 p
  rw [sub128, sub161]
  rfl
theorem sub163 (p : Pattern) : d123 (change p 132 (some 158)) = d123 p := by
  change (if p 159 then d55 (change p 132 (some 158)) else d121 (change p 132 (some 158))) = d123 p
  rw [sub128, sub162]
  rfl
theorem sub164 (p : Pattern) : d124 (change p 132 (some 158)) = d123 p := by
  change d123 (change p 132 (some 158)) = d123 p
  exact sub163 p
theorem sub165 (p : Pattern) : d125 (change p 132 (some 158)) = d125 p := by
  change (if p 187 then d60 (change p 132 (some 158)) else d11 (change p 132 (some 158))) = d125 p
  rw [sub141, sub136]
  rfl
theorem sub166 (p : Pattern) : d126 (change p 132 (some 158)) = d126 p := by
  change (if p 186 then d125 (change p 132 (some 158)) else d11 (change p 132 (some 158))) = d126 p
  rw [sub165, sub136]
  rfl
theorem sub167 (p : Pattern) : d127 (change p 132 (some 158)) = d127 p := by
  change (if p 168 then d126 (change p 132 (some 158)) else d120 (change p 132 (some 158))) = d127 p
  rw [sub166, sub161]
  rfl
theorem sub168 (p : Pattern) : d128 (change p 132 (some 158)) = d128 p := by
  change (if p 160 then d65 (change p 132 (some 158)) else d127 (change p 132 (some 158))) = d128 p
  rw [sub149, sub167]
  rfl
theorem sub169 (p : Pattern) : d130 (change p 132 (some 158)) = d130 p := by
  change (if p 159 then d65 (change p 132 (some 158)) else d128 (change p 132 (some 158))) = d130 p
  rw [sub149, sub168]
  rfl
theorem sub170 (p : Pattern) : d131 (change p 132 (some 158)) = d130 p := by
  change d130 (change p 132 (some 158)) = d130 p
  exact sub169 p
theorem sub171 (p : Pattern) : d132 (change p 132 (some 158)) = d745 p := by
  change (if p 141 then d131 (change p 132 (some 158)) else d124 (change p 132 (some 158))) = d745 p
  rw [sub170, sub164]
  rfl
theorem sub172 (p : Pattern) : d133 (change p 132 (some 158)) = d746 p := by
  change (if p 134 then d132 (change p 132 (some 158)) else d118 (change p 132 (some 158))) = d746 p
  rw [sub171, sub159]
  rfl
theorem sub173 (p : Pattern) : d134 (change p 132 (some 158)) = d747 p := by
  change (if p 133 then d133 (change p 132 (some 158)) else d113 (change p 132 (some 158))) = d747 p
  rw [sub172, sub154]
  rfl
theorem sub174 (p : Pattern) : d199 (change p 132 (some 158)) = d747 p := by
  change d134 (change p 132 (some 158)) = d747 p
  exact sub173 p
theorem sub175 (p : Pattern) : d66 (change p 132 (some 158)) = d66 p := by
  change (if p 141 then d65 (change p 132 (some 158)) else d55 (change p 132 (some 158))) = d66 p
  rw [sub149, sub128]
  rfl
theorem sub176 (p : Pattern) : d67 (change p 132 (some 158)) = d67 p := by
  change (if p 134 then d66 (change p 132 (some 158)) else d64 (change p 132 (some 158))) = d67 p
  rw [sub175, sub145]
  rfl
theorem sub177 (p : Pattern) : d137 (change p 132 (some 158)) = d137 p := by
  change (if p 186 then d55 (change p 132 (some 158)) else d119 (change p 132 (some 158))) = d137 p
  rw [sub128, sub160]
  rfl
theorem sub178 (p : Pattern) : d139 (change p 132 (some 158)) = d139 p := by
  change (if p 160 then d137 (change p 132 (some 158)) else d120 (change p 132 (some 158))) = d139 p
  rw [sub177, sub161]
  rfl
theorem sub179 (p : Pattern) : d141 (change p 132 (some 158)) = d141 p := by
  change (if p 159 then d55 (change p 132 (some 158)) else d139 (change p 132 (some 158))) = d141 p
  rw [sub128, sub178]
  rfl
theorem sub180 (p : Pattern) : d142 (change p 132 (some 158)) = d141 p := by
  change d141 (change p 132 (some 158)) = d141 p
  exact sub179 p
theorem sub181 (p : Pattern) : d143 (change p 132 (some 158)) = d143 p := by
  change (if p 186 then d60 (change p 132 (some 158)) else d125 (change p 132 (some 158))) = d143 p
  rw [sub141, sub165]
  rfl
theorem sub182 (p : Pattern) : d144 (change p 132 (some 158)) = d144 p := by
  change (if p 168 then d143 (change p 132 (some 158)) else d137 (change p 132 (some 158))) = d144 p
  rw [sub181, sub177]
  rfl
theorem sub183 (p : Pattern) : d146 (change p 132 (some 158)) = d146 p := by
  change (if p 160 then d144 (change p 132 (some 158)) else d127 (change p 132 (some 158))) = d146 p
  rw [sub182, sub167]
  rfl
theorem sub184 (p : Pattern) : d148 (change p 132 (some 158)) = d148 p := by
  change (if p 159 then d65 (change p 132 (some 158)) else d146 (change p 132 (some 158))) = d148 p
  rw [sub149, sub183]
  rfl
theorem sub185 (p : Pattern) : d149 (change p 132 (some 158)) = d148 p := by
  change d148 (change p 132 (some 158)) = d148 p
  exact sub184 p
theorem sub186 (p : Pattern) : d150 (change p 132 (some 158)) = d748 p := by
  change (if p 141 then d149 (change p 132 (some 158)) else d142 (change p 132 (some 158))) = d748 p
  rw [sub185, sub180]
  rfl
theorem sub187 (p : Pattern) : d151 (change p 132 (some 158)) = d749 p := by
  change (if p 134 then d66 (change p 132 (some 158)) else d150 (change p 132 (some 158))) = d749 p
  rw [sub175, sub186]
  rfl
theorem sub188 (p : Pattern) : d152 (change p 132 (some 158)) = d750 p := by
  change (if p 133 then d151 (change p 132 (some 158)) else d67 (change p 132 (some 158))) = d750 p
  rw [sub187, sub176]
  rfl
theorem sub189 (p : Pattern) : d200 (change p 132 (some 158)) = d750 p := by
  change d152 (change p 132 (some 158)) = d750 p
  exact sub188 p
theorem sub190 (p : Pattern) : d201 (change p 132 (some 158)) = d751 p := by
  change (if p 108 then d200 (change p 132 (some 158)) else d199 (change p 132 (some 158))) = d751 p
  rw [sub189, sub174]
  rfl
theorem sub191 (p : Pattern) : d0 (change p 134 (some 160)) = d0 p := by
  rfl
theorem sub192 (p : Pattern) : d2 (change p 134 (some 160)) = d2 p := by
  rfl
theorem sub193 (p : Pattern) : d6 (change p 134 (some 160)) = d6 p := by
  change (if p 193 then d2 (change p 134 (some 160)) else d0 (change p 134 (some 160))) = d6 p
  rw [sub192, sub191]
  rfl
theorem sub194 (p : Pattern) : d7 (change p 134 (some 160)) = d7 p := by
  change (if p 192 then d6 (change p 134 (some 160)) else d0 (change p 134 (some 160))) = d7 p
  rw [sub193, sub191]
  rfl
theorem sub195 (p : Pattern) : d4 (change p 134 (some 160)) = d4 p := by
  rfl
theorem sub196 (p : Pattern) : d54 (change p 134 (some 160)) = d54 p := by
  change (if p 193 then d4 (change p 134 (some 160)) else d2 (change p 134 (some 160))) = d54 p
  rw [sub195, sub192]
  rfl
theorem sub197 (p : Pattern) : d55 (change p 134 (some 160)) = d55 p := by
  change (if p 192 then d54 (change p 134 (some 160)) else d2 (change p 134 (some 160))) = d55 p
  rw [sub196, sub192]
  rfl
theorem sub198 (p : Pattern) : d56 (change p 134 (some 160)) = d56 p := by
  change (if p 186 then d55 (change p 134 (some 160)) else d7 (change p 134 (some 160))) = d56 p
  rw [sub197, sub194]
  rfl
theorem sub199 (p : Pattern) : d57 (change p 134 (some 160)) = d56 p := by
  change d56 (change p 134 (some 160)) = d56 p
  exact sub198 p
theorem sub200 (p : Pattern) : d1 (change p 134 (some 160)) = d1 p := by
  rfl
theorem sub201 (p : Pattern) : d8 (change p 134 (some 160)) = d8 p := by
  change (if p 271 then d1 (change p 134 (some 160)) else d0 (change p 134 (some 160))) = d8 p
  rw [sub200, sub191]
  rfl
theorem sub202 (p : Pattern) : d3 (change p 134 (some 160)) = d3 p := by
  rfl
theorem sub203 (p : Pattern) : d9 (change p 134 (some 160)) = d9 p := by
  change (if p 271 then d3 (change p 134 (some 160)) else d2 (change p 134 (some 160))) = d9 p
  rw [sub202, sub192]
  rfl
theorem sub204 (p : Pattern) : d10 (change p 134 (some 160)) = d10 p := by
  change (if p 193 then d9 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d10 p
  rw [sub203, sub201]
  rfl
theorem sub205 (p : Pattern) : d11 (change p 134 (some 160)) = d11 p := by
  change (if p 192 then d10 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d11 p
  rw [sub204, sub201]
  rfl
theorem sub206 (p : Pattern) : d5 (change p 134 (some 160)) = d5 p := by
  rfl
theorem sub207 (p : Pattern) : d58 (change p 134 (some 160)) = d58 p := by
  change (if p 271 then d5 (change p 134 (some 160)) else d4 (change p 134 (some 160))) = d58 p
  rw [sub206, sub195]
  rfl
theorem sub208 (p : Pattern) : d59 (change p 134 (some 160)) = d59 p := by
  change (if p 193 then d58 (change p 134 (some 160)) else d9 (change p 134 (some 160))) = d59 p
  rw [sub207, sub203]
  rfl
theorem sub209 (p : Pattern) : d60 (change p 134 (some 160)) = d60 p := by
  change (if p 192 then d59 (change p 134 (some 160)) else d9 (change p 134 (some 160))) = d60 p
  rw [sub208, sub203]
  rfl
theorem sub210 (p : Pattern) : d61 (change p 134 (some 160)) = d61 p := by
  change (if p 186 then d60 (change p 134 (some 160)) else d11 (change p 134 (some 160))) = d61 p
  rw [sub209, sub205]
  rfl
theorem sub211 (p : Pattern) : d62 (change p 134 (some 160)) = d62 p := by
  change (if p 168 then d61 (change p 134 (some 160)) else d56 (change p 134 (some 160))) = d62 p
  rw [sub210, sub198]
  rfl
theorem sub212 (p : Pattern) : d63 (change p 134 (some 160)) = d62 p := by
  change d62 (change p 134 (some 160)) = d62 p
  exact sub211 p
theorem sub213 (p : Pattern) : d64 (change p 134 (some 160)) = d451 p := by
  change (if p 141 then d63 (change p 134 (some 160)) else d57 (change p 134 (some 160))) = d451 p
  rw [sub212, sub199]
  rfl
theorem sub214 (p : Pattern) : d67 (change p 134 (some 160)) = d451 p := by
  change d64 (change p 134 (some 160)) = d451 p
  exact sub213 p
theorem sub215 (p : Pattern) : d68 (change p 134 (some 160)) = d456 p := by
  change (if p 158 then d55 (change p 134 (some 160)) else d57 (change p 134 (some 160))) = d456 p
  rw [sub197, sub199]
  rfl
theorem sub216 (p : Pattern) : d65 (change p 134 (some 160)) = d65 p := by
  change (if p 168 then d60 (change p 134 (some 160)) else d55 (change p 134 (some 160))) = d65 p
  rw [sub209, sub197]
  rfl
theorem sub217 (p : Pattern) : d69 (change p 134 (some 160)) = d457 p := by
  change (if p 158 then d65 (change p 134 (some 160)) else d63 (change p 134 (some 160))) = d457 p
  rw [sub216, sub212]
  rfl
theorem sub218 (p : Pattern) : d70 (change p 134 (some 160)) = d458 p := by
  change (if p 141 then d69 (change p 134 (some 160)) else d68 (change p 134 (some 160))) = d458 p
  rw [sub217, sub215]
  rfl
theorem sub219 (p : Pattern) : d71 (change p 134 (some 160)) = d458 p := by
  change d70 (change p 134 (some 160)) = d458 p
  exact sub218 p
theorem sub220 (p : Pattern) : d72 (change p 134 (some 160)) = d761 p := by
  change (if p 133 then d71 (change p 134 (some 160)) else d67 (change p 134 (some 160))) = d761 p
  rw [sub219, sub214]
  rfl
theorem sub221 (p : Pattern) : d66 (change p 134 (some 160)) = d66 p := by
  change (if p 141 then d65 (change p 134 (some 160)) else d55 (change p 134 (some 160))) = d66 p
  rw [sub216, sub197]
  rfl
theorem sub222 (p : Pattern) : d73 (change p 134 (some 160)) = d762 p := by
  change (if p 133 then d66 (change p 134 (some 160)) else d71 (change p 134 (some 160))) = d762 p
  rw [sub221, sub219]
  rfl
theorem sub223 (p : Pattern) : d74 (change p 134 (some 160)) = d763 p := by
  change (if p 132 then d73 (change p 134 (some 160)) else d72 (change p 134 (some 160))) = d763 p
  rw [sub222, sub220]
  rfl
theorem sub224 (p : Pattern) : d0 (change p 141 none) = d0 p := by
  rfl
theorem sub225 (p : Pattern) : d2 (change p 141 none) = d2 p := by
  rfl
theorem sub226 (p : Pattern) : d6 (change p 141 none) = d6 p := by
  change (if p 193 then d2 (change p 141 none) else d0 (change p 141 none)) = d6 p
  rw [sub225, sub224]
  rfl
theorem sub227 (p : Pattern) : d7 (change p 141 none) = d7 p := by
  change (if p 192 then d6 (change p 141 none) else d0 (change p 141 none)) = d7 p
  rw [sub226, sub224]
  rfl
theorem sub228 (p : Pattern) : d4 (change p 141 none) = d4 p := by
  rfl
theorem sub229 (p : Pattern) : d54 (change p 141 none) = d54 p := by
  change (if p 193 then d4 (change p 141 none) else d2 (change p 141 none)) = d54 p
  rw [sub228, sub225]
  rfl
theorem sub230 (p : Pattern) : d55 (change p 141 none) = d55 p := by
  change (if p 192 then d54 (change p 141 none) else d2 (change p 141 none)) = d55 p
  rw [sub229, sub225]
  rfl
theorem sub231 (p : Pattern) : d56 (change p 141 none) = d56 p := by
  change (if p 186 then d55 (change p 141 none) else d7 (change p 141 none)) = d56 p
  rw [sub230, sub227]
  rfl
theorem sub232 (p : Pattern) : d57 (change p 141 none) = d57 p := by
  change (if p 160 then d56 (change p 141 none) else d7 (change p 141 none)) = d57 p
  rw [sub231, sub227]
  rfl
theorem sub233 (p : Pattern) : d268 (change p 141 none) = d57 p := by
  change d57 (change p 141 none) = d57 p
  exact sub232 p
theorem sub234 (p : Pattern) : d106 (change p 141 none) = d106 p := by
  change (if p 160 then d55 (change p 141 none) else d7 (change p 141 none)) = d106 p
  rw [sub230, sub227]
  rfl
theorem sub235 (p : Pattern) : d119 (change p 141 none) = d119 p := by
  change (if p 187 then d55 (change p 141 none) else d7 (change p 141 none)) = d119 p
  rw [sub230, sub227]
  rfl
theorem sub236 (p : Pattern) : d120 (change p 141 none) = d120 p := by
  change (if p 186 then d119 (change p 141 none) else d7 (change p 141 none)) = d120 p
  rw [sub235, sub227]
  rfl
theorem sub237 (p : Pattern) : d121 (change p 141 none) = d121 p := by
  change (if p 160 then d55 (change p 141 none) else d120 (change p 141 none)) = d121 p
  rw [sub230, sub236]
  rfl
theorem sub238 (p : Pattern) : d122 (change p 141 none) = d122 p := by
  change (if p 159 then d121 (change p 141 none) else d106 (change p 141 none)) = d122 p
  rw [sub237, sub234]
  rfl
theorem sub239 (p : Pattern) : d179 (change p 141 none) = d179 p := by
  change (if p 158 then d122 (change p 141 none) else d106 (change p 141 none)) = d179 p
  rw [sub238, sub234]
  rfl
end NetHack.Sokoban12CostPartition
