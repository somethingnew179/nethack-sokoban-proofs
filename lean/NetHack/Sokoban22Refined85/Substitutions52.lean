/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions51
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6240 (p : Pattern) : d1130 (change p 162 (some 161)) = d1128 p := by
  change d1129 (change p 162 (some 161)) = d1128 p
  exact sub6239 p
theorem sub6241 (p : Pattern) : d1131 (change p 162 (some 161)) = d4842 p := by
  change (if p 160 then d1130 (change p 162 (some 161)) else d1125 (change p 162 (some 161))) = d4842 p
  rw [sub6240, sub6231]
  rfl
theorem sub6242 (p : Pattern) : d1132 (change p 162 (some 161)) = d4843 p := by
  change (if p 141 then d1131 (change p 162 (some 161)) else d1123 (change p 162 (some 161))) = d4843 p
  rw [sub6241, sub6226]
  rfl
theorem sub6243 (p : Pattern) : d1133 (change p 162 (some 161)) = d1133 p := by
  change (if p 163 then d132 (change p 162 (some 161)) else d269 (change p 162 (some 161))) = d1133 p
  rw [sub6144, sub6216]
  rfl
theorem sub6244 (p : Pattern) : d1134 (change p 162 (some 161)) = d1133 p := by
  change d1133 (change p 162 (some 161)) = d1133 p
  exact sub6243 p
theorem sub6245 (p : Pattern) : d1135 (change p 162 (some 161)) = d1133 p := by
  change d1134 (change p 162 (some 161)) = d1133 p
  exact sub6244 p
theorem sub6246 (p : Pattern) : d1136 (change p 162 (some 161)) = d4844 p := by
  change (if p 160 then d1062 (change p 162 (some 161)) else d1135 (change p 162 (some 161))) = d4844 p
  rw [sub6163, sub6245]
  rfl
theorem sub6247 (p : Pattern) : d1137 (change p 162 (some 161)) = d1137 p := by
  change (if p 163 then d109 (change p 162 (some 161)) else d298 (change p 162 (some 161))) = d1137 p
  rw [sub6165, sub6228]
  rfl
theorem sub6248 (p : Pattern) : d1138 (change p 162 (some 161)) = d1137 p := by
  change d1137 (change p 162 (some 161)) = d1137 p
  exact sub6247 p
theorem sub6249 (p : Pattern) : d1139 (change p 162 (some 161)) = d1137 p := by
  change d1138 (change p 162 (some 161)) = d1137 p
  exact sub6248 p
theorem sub6250 (p : Pattern) : d1141 (change p 162 (some 161)) = d12 p := by
  change d12 (change p 162 (some 161)) = d12 p
  exact sub6009 p
theorem sub6251 (p : Pattern) : d1142 (change p 162 (some 161)) = d4845 p := by
  change (if p 160 then d1141 (change p 162 (some 161)) else d1139 (change p 162 (some 161))) = d4845 p
  rw [sub6250, sub6249]
  rfl
theorem sub6252 (p : Pattern) : d1143 (change p 162 (some 161)) = d4846 p := by
  change (if p 141 then d1142 (change p 162 (some 161)) else d1136 (change p 162 (some 161))) = d4846 p
  rw [sub6251, sub6246]
  rfl
theorem sub6253 (p : Pattern) : d1144 (change p 162 (some 161)) = d4847 p := by
  change (if p 138 then d1143 (change p 162 (some 161)) else d1132 (change p 162 (some 161))) = d4847 p
  rw [sub6252, sub6242]
  rfl
theorem sub6254 (p : Pattern) : d1145 (change p 162 (some 161)) = d4848 p := by
  change (if p 138 then d12 (change p 162 (some 161)) else d1143 (change p 162 (some 161))) = d4848 p
  rw [sub6009, sub6252]
  rfl
theorem sub6255 (p : Pattern) : d1146 (change p 162 (some 161)) = d4849 p := by
  change (if p 116 then d1145 (change p 162 (some 161)) else d1144 (change p 162 (some 161))) = d4849 p
  rw [sub6254, sub6253]
  rfl
theorem sub6256 (p : Pattern) : d1147 (change p 162 (some 161)) = d4850 p := by
  change (if p 115 then d1146 (change p 162 (some 161)) else d1116 (change p 162 (some 161))) = d4850 p
  rw [sub6255, sub6214]
  rfl
theorem sub6257 (p : Pattern) : d1148 (change p 162 (some 161)) = d4851 p := by
  change (if p 71 then d1147 (change p 162 (some 161)) else d1014 (change p 162 (some 161))) = d4851 p
  rw [sub6256, sub6098]
  rfl
theorem sub6258 (p : Pattern) : d1149 (change p 162 (some 161)) = d4852 p := by
  change (if p 49 then d1148 (change p 162 (some 161)) else d1108 (change p 162 (some 161))) = d4852 p
  rw [sub6257, sub6207]
  rfl
theorem sub6259 (p : Pattern) : d1150 (change p 162 (some 161)) = d4853 p := by
  change (if p 48 then d1149 (change p 162 (some 161)) else d1098 (change p 162 (some 161))) = d4853 p
  rw [sub6258, sub6198]
  rfl
theorem sub6260 (p : Pattern) : d0 (change p 163 (some 162)) = d0 p := by
  rfl
theorem sub6261 (p : Pattern) : d12 (change p 163 (some 162)) = d12 p := by
  rfl
theorem sub6262 (p : Pattern) : d13 (change p 163 (some 162)) = d13 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d0 (change p 163 (some 162))) = d13 p
  rw [sub6261, sub6260]
  rfl
theorem sub6263 (p : Pattern) : d14 (change p 163 (some 162)) = d14 p := by
  change (if p 246 then d13 (change p 163 (some 162)) else d0 (change p 163 (some 162))) = d14 p
  rw [sub6262, sub6260]
  rfl
theorem sub6264 (p : Pattern) : d15 (change p 163 (some 162)) = d15 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d14 (change p 163 (some 162))) = d15 p
  rw [sub6261, sub6263]
  rfl
theorem sub6265 (p : Pattern) : d16 (change p 163 (some 162)) = d16 p := by
  change (if p 182 then d15 (change p 163 (some 162)) else d14 (change p 163 (some 162))) = d16 p
  rw [sub6264, sub6263]
  rfl
theorem sub6266 (p : Pattern) : d1152 (change p 163 (some 162)) = d16 p := by
  change d16 (change p 163 (some 162)) = d16 p
  exact sub6265 p
theorem sub6267 (p : Pattern) : d1153 (change p 163 (some 162)) = d16 p := by
  change d1152 (change p 163 (some 162)) = d16 p
  exact sub6266 p
theorem sub6268 (p : Pattern) : d9 (change p 163 (some 162)) = d9 p := by
  rfl
theorem sub6269 (p : Pattern) : d23 (change p 163 (some 162)) = d23 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d9 (change p 163 (some 162))) = d23 p
  rw [sub6261, sub6268]
  rfl
theorem sub6270 (p : Pattern) : d24 (change p 163 (some 162)) = d24 p := by
  change (if p 246 then d23 (change p 163 (some 162)) else d9 (change p 163 (some 162))) = d24 p
  rw [sub6269, sub6268]
  rfl
theorem sub6271 (p : Pattern) : d25 (change p 163 (some 162)) = d25 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d24 (change p 163 (some 162))) = d25 p
  rw [sub6261, sub6270]
  rfl
theorem sub6272 (p : Pattern) : d26 (change p 163 (some 162)) = d26 p := by
  change (if p 182 then d25 (change p 163 (some 162)) else d24 (change p 163 (some 162))) = d26 p
  rw [sub6271, sub6270]
  rfl
theorem sub6273 (p : Pattern) : d27 (change p 163 (some 162)) = d26 p := by
  change d26 (change p 163 (some 162)) = d26 p
  exact sub6272 p
theorem sub6274 (p : Pattern) : d1155 (change p 163 (some 162)) = d26 p := by
  change d27 (change p 163 (some 162)) = d26 p
  exact sub6273 p
theorem sub6275 (p : Pattern) : d1156 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1155 (change p 163 (some 162)) else d1153 (change p 163 (some 162))) = d4854 p
  rw [sub6274, sub6267]
  rfl
theorem sub6276 (p : Pattern) : d11 (change p 163 (some 162)) = d11 p := by
  rfl
theorem sub6277 (p : Pattern) : d39 (change p 163 (some 162)) = d39 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d11 (change p 163 (some 162))) = d39 p
  rw [sub6261, sub6276]
  rfl
theorem sub6278 (p : Pattern) : d40 (change p 163 (some 162)) = d40 p := by
  change (if p 246 then d39 (change p 163 (some 162)) else d11 (change p 163 (some 162))) = d40 p
  rw [sub6277, sub6276]
  rfl
theorem sub6279 (p : Pattern) : d41 (change p 163 (some 162)) = d41 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d40 (change p 163 (some 162))) = d41 p
  rw [sub6261, sub6278]
  rfl
theorem sub6280 (p : Pattern) : d42 (change p 163 (some 162)) = d42 p := by
  change (if p 182 then d41 (change p 163 (some 162)) else d14 (change p 163 (some 162))) = d42 p
  rw [sub6279, sub6263]
  rfl
theorem sub6281 (p : Pattern) : d1158 (change p 163 (some 162)) = d42 p := by
  change d42 (change p 163 (some 162)) = d42 p
  exact sub6280 p
theorem sub6282 (p : Pattern) : d1159 (change p 163 (some 162)) = d42 p := by
  change d1158 (change p 163 (some 162)) = d42 p
  exact sub6281 p
theorem sub6283 (p : Pattern) : d48 (change p 163 (some 162)) = d48 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d24 (change p 163 (some 162))) = d48 p
  rw [sub6261, sub6270]
  rfl
theorem sub6284 (p : Pattern) : d49 (change p 163 (some 162)) = d48 p := by
  change d48 (change p 163 (some 162)) = d48 p
  exact sub6283 p
theorem sub6285 (p : Pattern) : d1161 (change p 163 (some 162)) = d48 p := by
  change d49 (change p 163 (some 162)) = d48 p
  exact sub6284 p
theorem sub6286 (p : Pattern) : d1162 (change p 163 (some 162)) = d4855 p := by
  change (if p 161 then d1161 (change p 163 (some 162)) else d1159 (change p 163 (some 162))) = d4855 p
  rw [sub6285, sub6282]
  rfl
theorem sub6287 (p : Pattern) : d1163 (change p 163 (some 162)) = d4856 p := by
  change (if p 160 then d1162 (change p 163 (some 162)) else d1156 (change p 163 (some 162))) = d4856 p
  rw [sub6286, sub6275]
  rfl
theorem sub6288 (p : Pattern) : d2 (change p 163 (some 162)) = d2 p := by
  rfl
theorem sub6289 (p : Pattern) : d30 (change p 163 (some 162)) = d30 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d2 (change p 163 (some 162))) = d30 p
  rw [sub6261, sub6288]
  rfl
theorem sub6290 (p : Pattern) : d31 (change p 163 (some 162)) = d31 p := by
  change (if p 246 then d30 (change p 163 (some 162)) else d2 (change p 163 (some 162))) = d31 p
  rw [sub6289, sub6288]
  rfl
theorem sub6291 (p : Pattern) : d32 (change p 163 (some 162)) = d32 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d31 (change p 163 (some 162))) = d32 p
  rw [sub6261, sub6290]
  rfl
theorem sub6292 (p : Pattern) : d53 (change p 163 (some 162)) = d53 p := by
  change (if p 182 then d32 (change p 163 (some 162)) else d31 (change p 163 (some 162))) = d53 p
  rw [sub6291, sub6290]
  rfl
theorem sub6293 (p : Pattern) : d1165 (change p 163 (some 162)) = d53 p := by
  change d53 (change p 163 (some 162)) = d53 p
  exact sub6292 p
theorem sub6294 (p : Pattern) : d1166 (change p 163 (some 162)) = d53 p := by
  change d1165 (change p 163 (some 162)) = d53 p
  exact sub6293 p
theorem sub6295 (p : Pattern) : d62 (change p 163 (some 162)) = d62 p := by
  change (if p 182 then d41 (change p 163 (some 162)) else d40 (change p 163 (some 162))) = d62 p
  rw [sub6279, sub6278]
  rfl
theorem sub6296 (p : Pattern) : d63 (change p 163 (some 162)) = d62 p := by
  change d62 (change p 163 (some 162)) = d62 p
  exact sub6295 p
theorem sub6297 (p : Pattern) : d1168 (change p 163 (some 162)) = d62 p := by
  change d63 (change p 163 (some 162)) = d62 p
  exact sub6296 p
theorem sub6298 (p : Pattern) : d1169 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1168 (change p 163 (some 162)) else d1166 (change p 163 (some 162))) = d4857 p
  rw [sub6297, sub6294]
  rfl
theorem sub6299 (p : Pattern) : d66 (change p 163 (some 162)) = d66 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d31 (change p 163 (some 162))) = d66 p
  rw [sub6261, sub6290]
  rfl
theorem sub6300 (p : Pattern) : d1171 (change p 163 (some 162)) = d66 p := by
  change d66 (change p 163 (some 162)) = d66 p
  exact sub6299 p
theorem sub6301 (p : Pattern) : d1172 (change p 163 (some 162)) = d66 p := by
  change d1171 (change p 163 (some 162)) = d66 p
  exact sub6300 p
theorem sub6302 (p : Pattern) : d72 (change p 163 (some 162)) = d72 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d40 (change p 163 (some 162))) = d72 p
  rw [sub6261, sub6278]
  rfl
theorem sub6303 (p : Pattern) : d73 (change p 163 (some 162)) = d72 p := by
  change d72 (change p 163 (some 162)) = d72 p
  exact sub6302 p
theorem sub6304 (p : Pattern) : d1173 (change p 163 (some 162)) = d72 p := by
  change d73 (change p 163 (some 162)) = d72 p
  exact sub6303 p
theorem sub6305 (p : Pattern) : d1174 (change p 163 (some 162)) = d4858 p := by
  change (if p 161 then d1173 (change p 163 (some 162)) else d1172 (change p 163 (some 162))) = d4858 p
  rw [sub6304, sub6301]
  rfl
theorem sub6306 (p : Pattern) : d1175 (change p 163 (some 162)) = d4859 p := by
  change (if p 160 then d1174 (change p 163 (some 162)) else d1169 (change p 163 (some 162))) = d4859 p
  rw [sub6305, sub6298]
  rfl
theorem sub6307 (p : Pattern) : d1176 (change p 163 (some 162)) = d4860 p := by
  change (if p 141 then d1175 (change p 163 (some 162)) else d1163 (change p 163 (some 162))) = d4860 p
  rw [sub6306, sub6287]
  rfl
theorem sub6308 (p : Pattern) : d1177 (change p 163 (some 162)) = d16 p := by
  change d16 (change p 163 (some 162)) = d16 p
  exact sub6265 p
theorem sub6309 (p : Pattern) : d1178 (change p 163 (some 162)) = d16 p := by
  change d1177 (change p 163 (some 162)) = d16 p
  exact sub6308 p
theorem sub6310 (p : Pattern) : d1179 (change p 163 (some 162)) = d26 p := by
  change d27 (change p 163 (some 162)) = d26 p
  exact sub6273 p
theorem sub6311 (p : Pattern) : d1180 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1178 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6309]
  rfl
theorem sub6312 (p : Pattern) : d1182 (change p 163 (some 162)) = d62 p := by
  change d63 (change p 163 (some 162)) = d62 p
  exact sub6296 p
theorem sub6313 (p : Pattern) : d1183 (change p 163 (some 162)) = d4689 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d1182 (change p 163 (some 162))) = d4689 p
  rw [sub6261, sub6312]
  rfl
theorem sub6314 (p : Pattern) : d1184 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1180 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6311]
  rfl
theorem sub6315 (p : Pattern) : d1181 (change p 163 (some 162)) = d53 p := by
  change d53 (change p 163 (some 162)) = d53 p
  exact sub6292 p
theorem sub6316 (p : Pattern) : d1186 (change p 163 (some 162)) = d53 p := by
  change d1181 (change p 163 (some 162)) = d53 p
  exact sub6315 p
theorem sub6317 (p : Pattern) : d1187 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1186 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6316]
  rfl
theorem sub6318 (p : Pattern) : d1188 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6319 (p : Pattern) : d1189 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d1188 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6318]
  simp only [ite_self]
theorem sub6320 (p : Pattern) : d1190 (change p 163 (some 162)) = d4862 p := by
  change (if p 160 then d1189 (change p 163 (some 162)) else d1187 (change p 163 (some 162))) = d4862 p
  rw [sub6319, sub6317]
  rfl
theorem sub6321 (p : Pattern) : d1191 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1190 (change p 163 (some 162)) else d1184 (change p 163 (some 162))) = d4863 p
  rw [sub6320, sub6314]
  rfl
theorem sub6322 (p : Pattern) : d1192 (change p 163 (some 162)) = d4864 p := by
  change (if p 138 then d1191 (change p 163 (some 162)) else d1176 (change p 163 (some 162))) = d4864 p
  rw [sub6321, sub6307]
  rfl
theorem sub6323 (p : Pattern) : d1193 (change p 163 (some 162)) = d16 p := by
  change d16 (change p 163 (some 162)) = d16 p
  exact sub6265 p
theorem sub6324 (p : Pattern) : d1194 (change p 163 (some 162)) = d16 p := by
  change d1193 (change p 163 (some 162)) = d16 p
  exact sub6323 p
theorem sub6325 (p : Pattern) : d1195 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1194 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6324]
  rfl
theorem sub6326 (p : Pattern) : d1196 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1195 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6325]
  rfl
theorem sub6327 (p : Pattern) : d1198 (change p 163 (some 162)) = d53 p := by
  change d1181 (change p 163 (some 162)) = d53 p
  exact sub6315 p
theorem sub6328 (p : Pattern) : d1199 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1198 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6327]
  rfl
theorem sub6329 (p : Pattern) : d1200 (change p 163 (some 162)) = d4862 p := by
  change (if p 160 then d1189 (change p 163 (some 162)) else d1199 (change p 163 (some 162))) = d4862 p
  rw [sub6319, sub6328]
  rfl
theorem sub6330 (p : Pattern) : d1201 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1200 (change p 163 (some 162)) else d1196 (change p 163 (some 162))) = d4863 p
  rw [sub6329, sub6326]
  rfl
theorem sub6331 (p : Pattern) : d1202 (change p 163 (some 162)) = d62 p := by
  change d63 (change p 163 (some 162)) = d62 p
  exact sub6296 p
theorem sub6332 (p : Pattern) : d91 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6333 (p : Pattern) : d1203 (change p 163 (some 162)) = d4689 p := by
  change (if p 161 then d91 (change p 163 (some 162)) else d1202 (change p 163 (some 162))) = d4689 p
  rw [sub6332, sub6331]
  rfl
theorem sub6334 (p : Pattern) : d93 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d91 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6332]
  simp only [ite_self]
theorem sub6335 (p : Pattern) : d1204 (change p 163 (some 162)) = d4690 p := by
  change (if p 160 then d93 (change p 163 (some 162)) else d1203 (change p 163 (some 162))) = d4690 p
  rw [sub6334, sub6333]
  rfl
theorem sub6336 (p : Pattern) : d95 (change p 163 (some 162)) = d12 p := by
  change (if p 160 then d12 (change p 163 (some 162)) else d93 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6334]
  simp only [ite_self]
theorem sub6337 (p : Pattern) : d1205 (change p 163 (some 162)) = d4691 p := by
  change (if p 141 then d95 (change p 163 (some 162)) else d1204 (change p 163 (some 162))) = d4691 p
  rw [sub6336, sub6335]
  rfl
theorem sub6338 (p : Pattern) : d1206 (change p 163 (some 162)) = d4865 p := by
  change (if p 138 then d1205 (change p 163 (some 162)) else d1201 (change p 163 (some 162))) = d4865 p
  rw [sub6337, sub6330]
  rfl
theorem sub6339 (p : Pattern) : d1207 (change p 163 (some 162)) = d4866 p := by
  change (if p 116 then d1206 (change p 163 (some 162)) else d1192 (change p 163 (some 162))) = d4866 p
  rw [sub6338, sub6322]
  rfl
theorem sub6340 (p : Pattern) : d1185 (change p 163 (some 162)) = d16 p := by
  change d16 (change p 163 (some 162)) = d16 p
  exact sub6265 p
theorem sub6341 (p : Pattern) : d1209 (change p 163 (some 162)) = d16 p := by
  change d1185 (change p 163 (some 162)) = d16 p
  exact sub6340 p
theorem sub6342 (p : Pattern) : d1210 (change p 163 (some 162)) = d26 p := by
  change d27 (change p 163 (some 162)) = d26 p
  exact sub6273 p
theorem sub6343 (p : Pattern) : d1211 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1210 (change p 163 (some 162)) else d1209 (change p 163 (some 162))) = d4854 p
  rw [sub6342, sub6341]
  rfl
theorem sub6344 (p : Pattern) : d1213 (change p 163 (some 162)) = d42 p := by
  change d1158 (change p 163 (some 162)) = d42 p
  exact sub6281 p
theorem sub6345 (p : Pattern) : d1214 (change p 163 (some 162)) = d4855 p := by
  change (if p 161 then d1161 (change p 163 (some 162)) else d1213 (change p 163 (some 162))) = d4855 p
  rw [sub6285, sub6344]
  rfl
theorem sub6346 (p : Pattern) : d1215 (change p 163 (some 162)) = d4856 p := by
  change (if p 160 then d1214 (change p 163 (some 162)) else d1211 (change p 163 (some 162))) = d4856 p
  rw [sub6345, sub6343]
  rfl
theorem sub6347 (p : Pattern) : d1216 (change p 163 (some 162)) = d53 p := by
  change d1181 (change p 163 (some 162)) = d53 p
  exact sub6315 p
theorem sub6348 (p : Pattern) : d1217 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1216 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6347]
  rfl
theorem sub6349 (p : Pattern) : d1218 (change p 163 (some 162)) = d66 p := by
  change d1171 (change p 163 (some 162)) = d66 p
  exact sub6300 p
theorem sub6350 (p : Pattern) : d1219 (change p 163 (some 162)) = d4858 p := by
  change (if p 161 then d1173 (change p 163 (some 162)) else d1218 (change p 163 (some 162))) = d4858 p
  rw [sub6304, sub6349]
  rfl
theorem sub6351 (p : Pattern) : d1220 (change p 163 (some 162)) = d4859 p := by
  change (if p 160 then d1219 (change p 163 (some 162)) else d1217 (change p 163 (some 162))) = d4859 p
  rw [sub6350, sub6348]
  rfl
theorem sub6352 (p : Pattern) : d1221 (change p 163 (some 162)) = d4860 p := by
  change (if p 141 then d1220 (change p 163 (some 162)) else d1215 (change p 163 (some 162))) = d4860 p
  rw [sub6351, sub6346]
  rfl
theorem sub6353 (p : Pattern) : d1222 (change p 163 (some 162)) = d16 p := by
  change d1177 (change p 163 (some 162)) = d16 p
  exact sub6308 p
theorem sub6354 (p : Pattern) : d1223 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1222 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6353]
  rfl
theorem sub6355 (p : Pattern) : d1224 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1223 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6354]
  rfl
theorem sub6356 (p : Pattern) : d1225 (change p 163 (some 162)) = d53 p := by
  change d1181 (change p 163 (some 162)) = d53 p
  exact sub6315 p
theorem sub6357 (p : Pattern) : d1226 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1225 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6356]
  rfl
theorem sub6358 (p : Pattern) : d1227 (change p 163 (some 162)) = d4862 p := by
  change (if p 160 then d1189 (change p 163 (some 162)) else d1226 (change p 163 (some 162))) = d4862 p
  rw [sub6319, sub6357]
  rfl
theorem sub6359 (p : Pattern) : d1228 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1227 (change p 163 (some 162)) else d1224 (change p 163 (some 162))) = d4863 p
  rw [sub6358, sub6355]
  rfl
end NetHack.Sokoban22Refined85
