/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub120 (p : Pattern) : d6 (change p 10000 none) = d6 p := by
  change (if p 159 then d5 (change p 10000 none) else d4 (change p 10000 none)) = d6 p
  rw [sub119, sub118]
  rfl
theorem sub121 (p : Pattern) : d7 (change p 10000 none) = d7 p := by
  change (if p 159 then d2 (change p 10000 none) else d4 (change p 10000 none)) = d7 p
  rw [sub116, sub118]
  rfl
theorem sub122 (p : Pattern) : d8 (change p 10000 none) = d8 p := by
  change (if p 158 then d7 (change p 10000 none) else d6 (change p 10000 none)) = d8 p
  rw [sub121, sub120]
  rfl
theorem sub123 (p : Pattern) : d1 (change p 10000 none) = d1 p := by
  rfl
theorem sub124 (p : Pattern) : d9 (change p 10000 none) = d9 p := by
  change (if p 161 then d2 (change p 10000 none) else d1 (change p 10000 none)) = d9 p
  rw [sub116, sub123]
  rfl
theorem sub125 (p : Pattern) : d10 (change p 10000 none) = d10 p := by
  change (if p 160 then d9 (change p 10000 none) else d1 (change p 10000 none)) = d10 p
  rw [sub124, sub123]
  rfl
theorem sub126 (p : Pattern) : d11 (change p 10000 none) = d11 p := by
  change (if p 160 then d2 (change p 10000 none) else d1 (change p 10000 none)) = d11 p
  rw [sub116, sub123]
  rfl
theorem sub127 (p : Pattern) : d12 (change p 10000 none) = d12 p := by
  change (if p 159 then d11 (change p 10000 none) else d10 (change p 10000 none)) = d12 p
  rw [sub126, sub125]
  rfl
theorem sub128 (p : Pattern) : d13 (change p 10000 none) = d13 p := by
  change (if p 159 then d2 (change p 10000 none) else d10 (change p 10000 none)) = d13 p
  rw [sub116, sub125]
  rfl
theorem sub129 (p : Pattern) : d14 (change p 10000 none) = d14 p := by
  change (if p 158 then d13 (change p 10000 none) else d12 (change p 10000 none)) = d14 p
  rw [sub128, sub127]
  rfl
theorem sub130 (p : Pattern) : d15 (change p 10000 none) = d15 p := by
  change (if p 139 then d14 (change p 10000 none) else d8 (change p 10000 none)) = d15 p
  rw [sub129, sub122]
  rfl
theorem sub131 (p : Pattern) : d16 (change p 10000 none) = d16 p := by
  change (if p 138 then d15 (change p 10000 none) else d8 (change p 10000 none)) = d16 p
  rw [sub130, sub122]
  rfl
theorem sub132 (p : Pattern) : d17 (change p 10000 none) = d17 p := by
  change (if p 160 then d2 (change p 10000 none) else d3 (change p 10000 none)) = d17 p
  rw [sub116, sub117]
  rfl
theorem sub133 (p : Pattern) : d18 (change p 10000 none) = d18 p := by
  change (if p 159 then d17 (change p 10000 none) else d4 (change p 10000 none)) = d18 p
  rw [sub132, sub118]
  rfl
theorem sub134 (p : Pattern) : d19 (change p 10000 none) = d19 p := by
  change (if p 159 then d2 (change p 10000 none) else d17 (change p 10000 none)) = d19 p
  rw [sub116, sub132]
  rfl
theorem sub135 (p : Pattern) : d20 (change p 10000 none) = d20 p := by
  change (if p 158 then d19 (change p 10000 none) else d18 (change p 10000 none)) = d20 p
  rw [sub134, sub133]
  rfl
theorem sub136 (p : Pattern) : d21 (change p 10000 none) = d21 p := by
  change (if p 160 then d2 (change p 10000 none) else d9 (change p 10000 none)) = d21 p
  rw [sub116, sub124]
  rfl
theorem sub137 (p : Pattern) : d22 (change p 10000 none) = d22 p := by
  change (if p 159 then d21 (change p 10000 none) else d10 (change p 10000 none)) = d22 p
  rw [sub136, sub125]
  rfl
theorem sub138 (p : Pattern) : d23 (change p 10000 none) = d23 p := by
  change (if p 159 then d2 (change p 10000 none) else d21 (change p 10000 none)) = d23 p
  rw [sub116, sub136]
  rfl
theorem sub139 (p : Pattern) : d24 (change p 10000 none) = d24 p := by
  change (if p 158 then d23 (change p 10000 none) else d22 (change p 10000 none)) = d24 p
  rw [sub138, sub137]
  rfl
theorem sub140 (p : Pattern) : d25 (change p 10000 none) = d25 p := by
  change (if p 139 then d24 (change p 10000 none) else d20 (change p 10000 none)) = d25 p
  rw [sub139, sub135]
  rfl
theorem sub141 (p : Pattern) : d26 (change p 10000 none) = d26 p := by
  change (if p 138 then d25 (change p 10000 none) else d20 (change p 10000 none)) = d26 p
  rw [sub140, sub135]
  rfl
theorem sub142 (p : Pattern) : d27 (change p 10000 none) = d27 p := by
  change (if p 134 then d26 (change p 10000 none) else d16 (change p 10000 none)) = d27 p
  rw [sub141, sub131]
  rfl
theorem sub143 (p : Pattern) : d28 (change p 10000 none) = d28 p := by
  change (if p 133 then d27 (change p 10000 none) else d16 (change p 10000 none)) = d28 p
  rw [sub142, sub131]
  rfl
theorem sub144 (p : Pattern) : d29 (change p 10000 none) = d29 p := by
  change (if p 161 then d1 (change p 10000 none) else d0 (change p 10000 none)) = d29 p
  rw [sub123, sub115]
  rfl
theorem sub145 (p : Pattern) : d30 (change p 10000 none) = d30 p := by
  change (if p 160 then d2 (change p 10000 none) else d29 (change p 10000 none)) = d30 p
  rw [sub116, sub144]
  rfl
theorem sub146 (p : Pattern) : d31 (change p 10000 none) = d31 p := by
  change (if p 159 then d30 (change p 10000 none) else d4 (change p 10000 none)) = d31 p
  rw [sub145, sub118]
  rfl
theorem sub147 (p : Pattern) : d32 (change p 10000 none) = d32 p := by
  change (if p 159 then d2 (change p 10000 none) else d30 (change p 10000 none)) = d32 p
  rw [sub116, sub145]
  rfl
theorem sub148 (p : Pattern) : d33 (change p 10000 none) = d33 p := by
  change (if p 158 then d32 (change p 10000 none) else d31 (change p 10000 none)) = d33 p
  rw [sub147, sub146]
  rfl
theorem sub149 (p : Pattern) : d34 (change p 10000 none) = d34 p := by
  change (if p 139 then d24 (change p 10000 none) else d33 (change p 10000 none)) = d34 p
  rw [sub139, sub148]
  rfl
theorem sub150 (p : Pattern) : d35 (change p 10000 none) = d35 p := by
  change (if p 138 then d34 (change p 10000 none) else d33 (change p 10000 none)) = d35 p
  rw [sub149, sub148]
  rfl
theorem sub151 (p : Pattern) : d36 (change p 10000 none) = d36 p := by
  change (if p 134 then d35 (change p 10000 none) else d16 (change p 10000 none)) = d36 p
  rw [sub150, sub131]
  rfl
theorem sub152 (p : Pattern) : d37 (change p 10000 none) = d37 p := by
  change (if p 159 then d2 (change p 10000 none) else d5 (change p 10000 none)) = d37 p
  rw [sub116, sub119]
  rfl
theorem sub153 (p : Pattern) : d38 (change p 10000 none) = d38 p := by
  change (if p 158 then d37 (change p 10000 none) else d6 (change p 10000 none)) = d38 p
  rw [sub152, sub120]
  rfl
theorem sub154 (p : Pattern) : d39 (change p 10000 none) = d39 p := by
  change (if p 159 then d2 (change p 10000 none) else d11 (change p 10000 none)) = d39 p
  rw [sub116, sub126]
  rfl
theorem sub155 (p : Pattern) : d40 (change p 10000 none) = d40 p := by
  change (if p 158 then d39 (change p 10000 none) else d12 (change p 10000 none)) = d40 p
  rw [sub154, sub127]
  rfl
theorem sub156 (p : Pattern) : d41 (change p 10000 none) = d41 p := by
  change (if p 139 then d40 (change p 10000 none) else d38 (change p 10000 none)) = d41 p
  rw [sub155, sub153]
  rfl
theorem sub157 (p : Pattern) : d42 (change p 10000 none) = d42 p := by
  change (if p 138 then d41 (change p 10000 none) else d38 (change p 10000 none)) = d42 p
  rw [sub156, sub153]
  rfl
theorem sub158 (p : Pattern) : d43 (change p 10000 none) = d43 p := by
  change (if p 134 then d26 (change p 10000 none) else d42 (change p 10000 none)) = d43 p
  rw [sub141, sub157]
  rfl
theorem sub159 (p : Pattern) : d44 (change p 10000 none) = d44 p := by
  change (if p 133 then d43 (change p 10000 none) else d36 (change p 10000 none)) = d44 p
  rw [sub158, sub151]
  rfl
theorem sub160 (p : Pattern) : d45 (change p 10000 none) = d45 p := by
  change (if p 132 then d44 (change p 10000 none) else d28 (change p 10000 none)) = d45 p
  rw [sub159, sub143]
  rfl
theorem sub161 (p : Pattern) : d46 (change p 10000 none) = d46 p := by
  change (if p 134 then d25 (change p 10000 none) else d15 (change p 10000 none)) = d46 p
  rw [sub140, sub130]
  rfl
theorem sub162 (p : Pattern) : d47 (change p 10000 none) = d47 p := by
  change (if p 133 then d46 (change p 10000 none) else d15 (change p 10000 none)) = d47 p
  rw [sub161, sub130]
  rfl
theorem sub163 (p : Pattern) : d48 (change p 10000 none) = d48 p := by
  change (if p 134 then d34 (change p 10000 none) else d15 (change p 10000 none)) = d48 p
  rw [sub149, sub130]
  rfl
theorem sub164 (p : Pattern) : d49 (change p 10000 none) = d49 p := by
  change (if p 134 then d25 (change p 10000 none) else d41 (change p 10000 none)) = d49 p
  rw [sub140, sub156]
  rfl
theorem sub165 (p : Pattern) : d50 (change p 10000 none) = d50 p := by
  change (if p 133 then d49 (change p 10000 none) else d48 (change p 10000 none)) = d50 p
  rw [sub164, sub163]
  rfl
theorem sub166 (p : Pattern) : d51 (change p 10000 none) = d51 p := by
  change (if p 132 then d50 (change p 10000 none) else d47 (change p 10000 none)) = d51 p
  rw [sub165, sub162]
  rfl
theorem sub167 (p : Pattern) : d52 (change p 10000 none) = d52 p := by
  change (if p 139 then d2 (change p 10000 none) else d8 (change p 10000 none)) = d52 p
  rw [sub116, sub122]
  rfl
theorem sub168 (p : Pattern) : d53 (change p 10000 none) = d53 p := by
  change (if p 138 then d52 (change p 10000 none) else d15 (change p 10000 none)) = d53 p
  rw [sub167, sub130]
  rfl
theorem sub169 (p : Pattern) : d54 (change p 10000 none) = d54 p := by
  change (if p 139 then d2 (change p 10000 none) else d20 (change p 10000 none)) = d54 p
  rw [sub116, sub135]
  rfl
theorem sub170 (p : Pattern) : d55 (change p 10000 none) = d55 p := by
  change (if p 138 then d54 (change p 10000 none) else d25 (change p 10000 none)) = d55 p
  rw [sub169, sub140]
  rfl
theorem sub171 (p : Pattern) : d56 (change p 10000 none) = d56 p := by
  change (if p 134 then d55 (change p 10000 none) else d53 (change p 10000 none)) = d56 p
  rw [sub170, sub168]
  rfl
theorem sub172 (p : Pattern) : d57 (change p 10000 none) = d57 p := by
  change (if p 133 then d56 (change p 10000 none) else d53 (change p 10000 none)) = d57 p
  rw [sub171, sub168]
  rfl
theorem sub173 (p : Pattern) : d58 (change p 10000 none) = d58 p := by
  change (if p 139 then d2 (change p 10000 none) else d33 (change p 10000 none)) = d58 p
  rw [sub116, sub148]
  rfl
theorem sub174 (p : Pattern) : d59 (change p 10000 none) = d59 p := by
  change (if p 138 then d58 (change p 10000 none) else d34 (change p 10000 none)) = d59 p
  rw [sub173, sub149]
  rfl
theorem sub175 (p : Pattern) : d60 (change p 10000 none) = d60 p := by
  change (if p 134 then d59 (change p 10000 none) else d53 (change p 10000 none)) = d60 p
  rw [sub174, sub168]
  rfl
theorem sub176 (p : Pattern) : d61 (change p 10000 none) = d61 p := by
  change (if p 139 then d2 (change p 10000 none) else d38 (change p 10000 none)) = d61 p
  rw [sub116, sub153]
  rfl
theorem sub177 (p : Pattern) : d62 (change p 10000 none) = d62 p := by
  change (if p 138 then d61 (change p 10000 none) else d41 (change p 10000 none)) = d62 p
  rw [sub176, sub156]
  rfl
theorem sub178 (p : Pattern) : d63 (change p 10000 none) = d63 p := by
  change (if p 134 then d55 (change p 10000 none) else d62 (change p 10000 none)) = d63 p
  rw [sub170, sub177]
  rfl
theorem sub179 (p : Pattern) : d64 (change p 10000 none) = d64 p := by
  change (if p 133 then d63 (change p 10000 none) else d60 (change p 10000 none)) = d64 p
  rw [sub178, sub175]
  rfl
theorem sub180 (p : Pattern) : d65 (change p 10000 none) = d65 p := by
  change (if p 132 then d64 (change p 10000 none) else d57 (change p 10000 none)) = d65 p
  rw [sub179, sub172]
  rfl
theorem sub181 (p : Pattern) : d66 (change p 10000 none) = d66 p := by
  change (if p 113 then d65 (change p 10000 none) else d51 (change p 10000 none)) = d66 p
  rw [sub180, sub166]
  rfl
theorem sub182 (p : Pattern) : d67 (change p 10000 none) = d67 p := by
  change (if p 112 then d66 (change p 10000 none) else d45 (change p 10000 none)) = d67 p
  rw [sub181, sub160]
  rfl
theorem sub183 (p : Pattern) : d68 (change p 10000 none) = d68 p := by
  change (if p 139 then d2 (change p 10000 none) else d40 (change p 10000 none)) = d68 p
  rw [sub116, sub155]
  rfl
theorem sub184 (p : Pattern) : d69 (change p 10000 none) = d69 p := by
  change (if p 138 then d68 (change p 10000 none) else d40 (change p 10000 none)) = d69 p
  rw [sub183, sub155]
  rfl
theorem sub185 (p : Pattern) : d70 (change p 10000 none) = d70 p := by
  change (if p 139 then d2 (change p 10000 none) else d24 (change p 10000 none)) = d70 p
  rw [sub116, sub139]
  rfl
theorem sub186 (p : Pattern) : d71 (change p 10000 none) = d71 p := by
  change (if p 138 then d70 (change p 10000 none) else d24 (change p 10000 none)) = d71 p
  rw [sub185, sub139]
  rfl
theorem sub187 (p : Pattern) : d72 (change p 10000 none) = d72 p := by
  change (if p 134 then d71 (change p 10000 none) else d69 (change p 10000 none)) = d72 p
  rw [sub186, sub184]
  rfl
theorem sub188 (p : Pattern) : d73 (change p 10000 none) = d73 p := by
  change (if p 133 then d72 (change p 10000 none) else d27 (change p 10000 none)) = d73 p
  rw [sub187, sub142]
  rfl
theorem sub189 (p : Pattern) : d74 (change p 10000 none) = d74 p := by
  change (if p 132 then d73 (change p 10000 none) else d28 (change p 10000 none)) = d74 p
  rw [sub188, sub143]
  rfl
theorem sub190 (p : Pattern) : d75 (change p 10000 none) = d75 p := by
  change (if p 134 then d70 (change p 10000 none) else d68 (change p 10000 none)) = d75 p
  rw [sub185, sub183]
  rfl
theorem sub191 (p : Pattern) : d76 (change p 10000 none) = d76 p := by
  change (if p 133 then d75 (change p 10000 none) else d27 (change p 10000 none)) = d76 p
  rw [sub190, sub142]
  rfl
theorem sub192 (p : Pattern) : d77 (change p 10000 none) = d77 p := by
  change (if p 132 then d76 (change p 10000 none) else d28 (change p 10000 none)) = d77 p
  rw [sub191, sub143]
  rfl
theorem sub193 (p : Pattern) : d78 (change p 10000 none) = d78 p := by
  change (if p 113 then d77 (change p 10000 none) else d74 (change p 10000 none)) = d78 p
  rw [sub192, sub189]
  rfl
theorem sub194 (p : Pattern) : d79 (change p 10000 none) = d79 p := by
  change (if p 133 then d75 (change p 10000 none) else d46 (change p 10000 none)) = d79 p
  rw [sub190, sub161]
  rfl
theorem sub195 (p : Pattern) : d80 (change p 10000 none) = d80 p := by
  change (if p 132 then d79 (change p 10000 none) else d47 (change p 10000 none)) = d80 p
  rw [sub194, sub162]
  rfl
theorem sub196 (p : Pattern) : d81 (change p 10000 none) = d81 p := by
  change (if p 133 then d75 (change p 10000 none) else d56 (change p 10000 none)) = d81 p
  rw [sub190, sub171]
  rfl
theorem sub197 (p : Pattern) : d82 (change p 10000 none) = d82 p := by
  change (if p 132 then d81 (change p 10000 none) else d57 (change p 10000 none)) = d82 p
  rw [sub196, sub172]
  rfl
theorem sub198 (p : Pattern) : d83 (change p 10000 none) = d83 p := by
  change (if p 113 then d82 (change p 10000 none) else d80 (change p 10000 none)) = d83 p
  rw [sub197, sub195]
  rfl
theorem sub199 (p : Pattern) : d84 (change p 10000 none) = d84 p := by
  change (if p 112 then d83 (change p 10000 none) else d78 (change p 10000 none)) = d84 p
  rw [sub198, sub193]
  rfl
theorem sub200 (p : Pattern) : d85 (change p 10000 none) = d85 p := by
  change (if p 106 then d84 (change p 10000 none) else d67 (change p 10000 none)) = d85 p
  rw [sub199, sub182]
  rfl
theorem sub201 (p : Pattern) : d86 (change p 10000 none) = d86 p := by
  change (if p 138 then d52 (change p 10000 none) else d8 (change p 10000 none)) = d86 p
  rw [sub167, sub122]
  rfl
theorem sub202 (p : Pattern) : d87 (change p 10000 none) = d87 p := by
  change (if p 138 then d54 (change p 10000 none) else d20 (change p 10000 none)) = d87 p
  rw [sub169, sub135]
  rfl
theorem sub203 (p : Pattern) : d88 (change p 10000 none) = d88 p := by
  change (if p 134 then d87 (change p 10000 none) else d86 (change p 10000 none)) = d88 p
  rw [sub202, sub201]
  rfl
theorem sub204 (p : Pattern) : d89 (change p 10000 none) = d89 p := by
  change (if p 133 then d88 (change p 10000 none) else d86 (change p 10000 none)) = d89 p
  rw [sub203, sub201]
  rfl
theorem sub205 (p : Pattern) : d90 (change p 10000 none) = d90 p := by
  change (if p 138 then d58 (change p 10000 none) else d33 (change p 10000 none)) = d90 p
  rw [sub173, sub148]
  rfl
theorem sub206 (p : Pattern) : d91 (change p 10000 none) = d91 p := by
  change (if p 134 then d90 (change p 10000 none) else d86 (change p 10000 none)) = d91 p
  rw [sub205, sub201]
  rfl
theorem sub207 (p : Pattern) : d92 (change p 10000 none) = d92 p := by
  change (if p 138 then d61 (change p 10000 none) else d38 (change p 10000 none)) = d92 p
  rw [sub176, sub153]
  rfl
theorem sub208 (p : Pattern) : d93 (change p 10000 none) = d93 p := by
  change (if p 134 then d87 (change p 10000 none) else d92 (change p 10000 none)) = d93 p
  rw [sub202, sub207]
  rfl
theorem sub209 (p : Pattern) : d94 (change p 10000 none) = d94 p := by
  change (if p 133 then d93 (change p 10000 none) else d91 (change p 10000 none)) = d94 p
  rw [sub208, sub206]
  rfl
theorem sub210 (p : Pattern) : d95 (change p 10000 none) = d95 p := by
  change (if p 132 then d94 (change p 10000 none) else d89 (change p 10000 none)) = d95 p
  rw [sub209, sub204]
  rfl
theorem sub211 (p : Pattern) : d96 (change p 10000 none) = d96 p := by
  change (if p 113 then d95 (change p 10000 none) else d45 (change p 10000 none)) = d96 p
  rw [sub210, sub160]
  rfl
theorem sub212 (p : Pattern) : d97 (change p 10000 none) = d97 p := by
  change (if p 139 then d2 (change p 10000 none) else d14 (change p 10000 none)) = d97 p
  rw [sub116, sub129]
  rfl
theorem sub213 (p : Pattern) : d98 (change p 10000 none) = d98 p := by
  change (if p 138 then d97 (change p 10000 none) else d14 (change p 10000 none)) = d98 p
  rw [sub212, sub129]
  rfl
theorem sub214 (p : Pattern) : d99 (change p 10000 none) = d99 p := by
  change (if p 134 then d71 (change p 10000 none) else d98 (change p 10000 none)) = d99 p
  rw [sub186, sub213]
  rfl
theorem sub215 (p : Pattern) : d100 (change p 10000 none) = d100 p := by
  change (if p 133 then d99 (change p 10000 none) else d98 (change p 10000 none)) = d100 p
  rw [sub214, sub213]
  rfl
theorem sub216 (p : Pattern) : d101 (change p 10000 none) = d101 p := by
  change (if p 133 then d72 (change p 10000 none) else d99 (change p 10000 none)) = d101 p
  rw [sub187, sub214]
  rfl
theorem sub217 (p : Pattern) : d102 (change p 10000 none) = d102 p := by
  change (if p 132 then d101 (change p 10000 none) else d100 (change p 10000 none)) = d102 p
  rw [sub216, sub215]
  rfl
theorem sub218 (p : Pattern) : d103 (change p 10000 none) = d103 p := by
  change (if p 112 then d102 (change p 10000 none) else d96 (change p 10000 none)) = d103 p
  rw [sub217, sub211]
  rfl
theorem sub219 (p : Pattern) : d104 (change p 10000 none) = d104 p := by
  change (if p 133 then d75 (change p 10000 none) else d88 (change p 10000 none)) = d104 p
  rw [sub190, sub203]
  rfl
theorem sub220 (p : Pattern) : d105 (change p 10000 none) = d105 p := by
  change (if p 132 then d104 (change p 10000 none) else d89 (change p 10000 none)) = d105 p
  rw [sub219, sub204]
  rfl
theorem sub221 (p : Pattern) : d106 (change p 10000 none) = d106 p := by
  change (if p 113 then d105 (change p 10000 none) else d77 (change p 10000 none)) = d106 p
  rw [sub220, sub192]
  rfl
theorem sub222 (p : Pattern) : d107 (change p 10000 none) = d107 p := by
  change (if p 133 then d2 (change p 10000 none) else d99 (change p 10000 none)) = d107 p
  rw [sub116, sub214]
  rfl
theorem sub223 (p : Pattern) : d108 (change p 10000 none) = d108 p := by
  change (if p 132 then d107 (change p 10000 none) else d100 (change p 10000 none)) = d108 p
  rw [sub222, sub215]
  rfl
theorem sub224 (p : Pattern) : d109 (change p 10000 none) = d109 p := by
  change (if p 134 then d70 (change p 10000 none) else d97 (change p 10000 none)) = d109 p
  rw [sub185, sub212]
  rfl
theorem sub225 (p : Pattern) : d110 (change p 10000 none) = d110 p := by
  change (if p 133 then d109 (change p 10000 none) else d97 (change p 10000 none)) = d110 p
  rw [sub224, sub212]
  rfl
theorem sub226 (p : Pattern) : d111 (change p 10000 none) = d111 p := by
  change (if p 133 then d2 (change p 10000 none) else d109 (change p 10000 none)) = d111 p
  rw [sub116, sub224]
  rfl
theorem sub227 (p : Pattern) : d112 (change p 10000 none) = d112 p := by
  change (if p 132 then d111 (change p 10000 none) else d110 (change p 10000 none)) = d112 p
  rw [sub226, sub225]
  rfl
theorem sub228 (p : Pattern) : d113 (change p 10000 none) = d113 p := by
  change (if p 113 then d112 (change p 10000 none) else d108 (change p 10000 none)) = d113 p
  rw [sub227, sub223]
  rfl
theorem sub229 (p : Pattern) : d114 (change p 10000 none) = d114 p := by
  change (if p 112 then d113 (change p 10000 none) else d106 (change p 10000 none)) = d114 p
  rw [sub228, sub221]
  rfl
theorem sub230 (p : Pattern) : d115 (change p 10000 none) = d115 p := by
  change (if p 106 then d114 (change p 10000 none) else d103 (change p 10000 none)) = d115 p
  rw [sub229, sub218]
  rfl
theorem sub231 (p : Pattern) : d116 (change p 10000 none) = d116 p := by
  change (if p 86 then d115 (change p 10000 none) else d85 (change p 10000 none)) = d116 p
  rw [sub230, sub200]
  rfl
theorem sub232 (p : Pattern) : d117 (change p 10000 none) = d117 p := by
  change (if p 112 then d83 (change p 10000 none) else d77 (change p 10000 none)) = d117 p
  rw [sub198, sub192]
  rfl
theorem sub233 (p : Pattern) : d118 (change p 10000 none) = d118 p := by
  change (if p 106 then d117 (change p 10000 none) else d67 (change p 10000 none)) = d118 p
  rw [sub232, sub182]
  rfl
theorem sub234 (p : Pattern) : d119 (change p 10000 none) = d119 p := by
  change (if p 139 then d20 (change p 10000 none) else d33 (change p 10000 none)) = d119 p
  rw [sub135, sub148]
  rfl
theorem sub235 (p : Pattern) : d120 (change p 10000 none) = d120 p := by
  change (if p 138 then d58 (change p 10000 none) else d119 (change p 10000 none)) = d120 p
  rw [sub173, sub234]
  rfl
theorem sub236 (p : Pattern) : d121 (change p 10000 none) = d121 p := by
  change (if p 134 then d120 (change p 10000 none) else d86 (change p 10000 none)) = d121 p
  rw [sub235, sub201]
  rfl
theorem sub237 (p : Pattern) : d122 (change p 10000 none) = d122 p := by
  change (if p 133 then d93 (change p 10000 none) else d121 (change p 10000 none)) = d122 p
  rw [sub208, sub236]
  rfl
theorem sub238 (p : Pattern) : d123 (change p 10000 none) = d123 p := by
  change (if p 132 then d122 (change p 10000 none) else d89 (change p 10000 none)) = d123 p
  rw [sub237, sub204]
  rfl
theorem sub239 (p : Pattern) : d124 (change p 10000 none) = d124 p := by
  change (if p 113 then d123 (change p 10000 none) else d45 (change p 10000 none)) = d124 p
  rw [sub238, sub160]
  rfl
end NetHack.Sokoban32Refined
