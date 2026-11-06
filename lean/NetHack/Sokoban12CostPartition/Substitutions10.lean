/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1200 (p : Pattern) : d319 (change p 158 (some 159)) = d998 p := by
  change (if p 108 then d318 (change p 158 (some 159)) else d316 (change p 158 (some 159))) = d998 p
  rw [sub1199, sub1178]
  rfl
theorem sub1201 (p : Pattern) : d237 (change p 10000 none) = d237 p := by
  change (if p 158 then d129 (change p 10000 none) else d109 (change p 10000 none)) = d237 p
  rw [sub89, sub69]
  rfl
theorem sub1202 (p : Pattern) : d238 (change p 10000 none) = d238 p := by
  change (if p 141 then d237 (change p 10000 none) else d179 (change p 10000 none)) = d238 p
  rw [sub1201, sub269]
  rfl
theorem sub1203 (p : Pattern) : d239 (change p 10000 none) = d239 p := by
  change (if p 134 then d238 (change p 10000 none) else d64 (change p 10000 none)) = d239 p
  rw [sub1202, sub23]
  rfl
theorem sub1204 (p : Pattern) : d240 (change p 10000 none) = d240 p := by
  change (if p 158 then d65 (change p 10000 none) else d129 (change p 10000 none)) = d240 p
  rw [sub24, sub89]
  rfl
theorem sub1205 (p : Pattern) : d241 (change p 10000 none) = d241 p := by
  change (if p 141 then d240 (change p 10000 none) else d181 (change p 10000 none)) = d241 p
  rw [sub1204, sub271]
  rfl
theorem sub1206 (p : Pattern) : d242 (change p 10000 none) = d242 p := by
  change (if p 134 then d241 (change p 10000 none) else d70 (change p 10000 none)) = d242 p
  rw [sub1205, sub29]
  rfl
theorem sub1207 (p : Pattern) : d243 (change p 10000 none) = d243 p := by
  change (if p 133 then d242 (change p 10000 none) else d239 (change p 10000 none)) = d243 p
  rw [sub1206, sub1203]
  rfl
theorem sub1208 (p : Pattern) : d244 (change p 10000 none) = d244 p := by
  change (if p 133 then d66 (change p 10000 none) else d242 (change p 10000 none)) = d244 p
  rw [sub25, sub1206]
  rfl
theorem sub1209 (p : Pattern) : d245 (change p 10000 none) = d245 p := by
  change (if p 132 then d244 (change p 10000 none) else d243 (change p 10000 none)) = d245 p
  rw [sub1208, sub1207]
  rfl
theorem sub1210 (p : Pattern) : d246 (change p 10000 none) = d246 p := by
  change (if p 158 then d155 (change p 10000 none) else d63 (change p 10000 none)) = d246 p
  rw [sub115, sub22]
  rfl
theorem sub1211 (p : Pattern) : d247 (change p 10000 none) = d247 p := by
  change (if p 141 then d246 (change p 10000 none) else d186 (change p 10000 none)) = d247 p
  rw [sub1210, sub276]
  rfl
theorem sub1212 (p : Pattern) : d248 (change p 10000 none) = d248 p := by
  change (if p 134 then d66 (change p 10000 none) else d247 (change p 10000 none)) = d248 p
  rw [sub25, sub1211]
  rfl
theorem sub1213 (p : Pattern) : d249 (change p 10000 none) = d249 p := by
  change (if p 158 then d65 (change p 10000 none) else d147 (change p 10000 none)) = d249 p
  rw [sub24, sub107]
  rfl
theorem sub1214 (p : Pattern) : d250 (change p 10000 none) = d250 p := by
  change (if p 141 then d249 (change p 10000 none) else d188 (change p 10000 none)) = d250 p
  rw [sub1213, sub278]
  rfl
theorem sub1215 (p : Pattern) : d251 (change p 10000 none) = d251 p := by
  change (if p 134 then d66 (change p 10000 none) else d250 (change p 10000 none)) = d251 p
  rw [sub25, sub1214]
  rfl
theorem sub1216 (p : Pattern) : d252 (change p 10000 none) = d252 p := by
  change (if p 133 then d251 (change p 10000 none) else d248 (change p 10000 none)) = d252 p
  rw [sub1215, sub1212]
  rfl
theorem sub1217 (p : Pattern) : d253 (change p 10000 none) = d253 p := by
  change (if p 158 then d65 (change p 10000 none) else d155 (change p 10000 none)) = d253 p
  rw [sub24, sub115]
  rfl
theorem sub1218 (p : Pattern) : d254 (change p 10000 none) = d254 p := by
  change (if p 141 then d253 (change p 10000 none) else d191 (change p 10000 none)) = d254 p
  rw [sub1217, sub281]
  rfl
theorem sub1219 (p : Pattern) : d255 (change p 10000 none) = d255 p := by
  change (if p 134 then d66 (change p 10000 none) else d254 (change p 10000 none)) = d255 p
  rw [sub25, sub1218]
  rfl
theorem sub1220 (p : Pattern) : d256 (change p 10000 none) = d256 p := by
  change (if p 133 then d66 (change p 10000 none) else d255 (change p 10000 none)) = d256 p
  rw [sub25, sub1219]
  rfl
theorem sub1221 (p : Pattern) : d257 (change p 10000 none) = d257 p := by
  change (if p 132 then d256 (change p 10000 none) else d252 (change p 10000 none)) = d257 p
  rw [sub1220, sub1216]
  rfl
theorem sub1222 (p : Pattern) : d258 (change p 10000 none) = d258 p := by
  change (if p 108 then d257 (change p 10000 none) else d245 (change p 10000 none)) = d258 p
  rw [sub1221, sub1209]
  rfl
theorem sub1223 (p : Pattern) : d0 (change p 159 (some 160)) = d0 p := by
  rfl
theorem sub1224 (p : Pattern) : d2 (change p 159 (some 160)) = d2 p := by
  rfl
theorem sub1225 (p : Pattern) : d6 (change p 159 (some 160)) = d6 p := by
  change (if p 193 then d2 (change p 159 (some 160)) else d0 (change p 159 (some 160))) = d6 p
  rw [sub1224, sub1223]
  rfl
theorem sub1226 (p : Pattern) : d7 (change p 159 (some 160)) = d7 p := by
  change (if p 192 then d6 (change p 159 (some 160)) else d0 (change p 159 (some 160))) = d7 p
  rw [sub1225, sub1223]
  rfl
theorem sub1227 (p : Pattern) : d4 (change p 159 (some 160)) = d4 p := by
  rfl
theorem sub1228 (p : Pattern) : d54 (change p 159 (some 160)) = d54 p := by
  change (if p 193 then d4 (change p 159 (some 160)) else d2 (change p 159 (some 160))) = d54 p
  rw [sub1227, sub1224]
  rfl
theorem sub1229 (p : Pattern) : d55 (change p 159 (some 160)) = d55 p := by
  change (if p 192 then d54 (change p 159 (some 160)) else d2 (change p 159 (some 160))) = d55 p
  rw [sub1228, sub1224]
  rfl
theorem sub1230 (p : Pattern) : d56 (change p 159 (some 160)) = d56 p := by
  change (if p 186 then d55 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d56 p
  rw [sub1229, sub1226]
  rfl
theorem sub1231 (p : Pattern) : d57 (change p 159 (some 160)) = d56 p := by
  change d56 (change p 159 (some 160)) = d56 p
  exact sub1230 p
theorem sub1232 (p : Pattern) : d114 (change p 159 (some 160)) = d56 p := by
  change d57 (change p 159 (some 160)) = d56 p
  exact sub1231 p
theorem sub1233 (p : Pattern) : d1 (change p 159 (some 160)) = d1 p := by
  rfl
theorem sub1234 (p : Pattern) : d8 (change p 159 (some 160)) = d8 p := by
  change (if p 271 then d1 (change p 159 (some 160)) else d0 (change p 159 (some 160))) = d8 p
  rw [sub1233, sub1223]
  rfl
theorem sub1235 (p : Pattern) : d3 (change p 159 (some 160)) = d3 p := by
  rfl
theorem sub1236 (p : Pattern) : d9 (change p 159 (some 160)) = d9 p := by
  change (if p 271 then d3 (change p 159 (some 160)) else d2 (change p 159 (some 160))) = d9 p
  rw [sub1235, sub1224]
  rfl
theorem sub1237 (p : Pattern) : d10 (change p 159 (some 160)) = d10 p := by
  change (if p 193 then d9 (change p 159 (some 160)) else d8 (change p 159 (some 160))) = d10 p
  rw [sub1236, sub1234]
  rfl
theorem sub1238 (p : Pattern) : d11 (change p 159 (some 160)) = d11 p := by
  change (if p 192 then d10 (change p 159 (some 160)) else d8 (change p 159 (some 160))) = d11 p
  rw [sub1237, sub1234]
  rfl
theorem sub1239 (p : Pattern) : d5 (change p 159 (some 160)) = d5 p := by
  rfl
theorem sub1240 (p : Pattern) : d58 (change p 159 (some 160)) = d58 p := by
  change (if p 271 then d5 (change p 159 (some 160)) else d4 (change p 159 (some 160))) = d58 p
  rw [sub1239, sub1227]
  rfl
theorem sub1241 (p : Pattern) : d59 (change p 159 (some 160)) = d59 p := by
  change (if p 193 then d58 (change p 159 (some 160)) else d9 (change p 159 (some 160))) = d59 p
  rw [sub1240, sub1236]
  rfl
theorem sub1242 (p : Pattern) : d60 (change p 159 (some 160)) = d60 p := by
  change (if p 192 then d59 (change p 159 (some 160)) else d9 (change p 159 (some 160))) = d60 p
  rw [sub1241, sub1236]
  rfl
theorem sub1243 (p : Pattern) : d61 (change p 159 (some 160)) = d61 p := by
  change (if p 186 then d60 (change p 159 (some 160)) else d11 (change p 159 (some 160))) = d61 p
  rw [sub1242, sub1238]
  rfl
theorem sub1244 (p : Pattern) : d62 (change p 159 (some 160)) = d62 p := by
  change (if p 168 then d61 (change p 159 (some 160)) else d56 (change p 159 (some 160))) = d62 p
  rw [sub1243, sub1230]
  rfl
theorem sub1245 (p : Pattern) : d63 (change p 159 (some 160)) = d62 p := by
  change d62 (change p 159 (some 160)) = d62 p
  exact sub1244 p
theorem sub1246 (p : Pattern) : d116 (change p 159 (some 160)) = d62 p := by
  change d63 (change p 159 (some 160)) = d62 p
  exact sub1245 p
theorem sub1247 (p : Pattern) : d335 (change p 159 (some 160)) = d451 p := by
  change (if p 141 then d116 (change p 159 (some 160)) else d114 (change p 159 (some 160))) = d451 p
  rw [sub1246, sub1232]
  rfl
theorem sub1248 (p : Pattern) : d106 (change p 159 (some 160)) = d55 p := by
  change d55 (change p 159 (some 160)) = d55 p
  exact sub1229 p
theorem sub1249 (p : Pattern) : d107 (change p 159 (some 160)) = d55 p := by
  change d106 (change p 159 (some 160)) = d55 p
  exact sub1248 p
theorem sub1250 (p : Pattern) : d65 (change p 159 (some 160)) = d65 p := by
  change (if p 168 then d60 (change p 159 (some 160)) else d55 (change p 159 (some 160))) = d65 p
  rw [sub1242, sub1229]
  rfl
theorem sub1251 (p : Pattern) : d109 (change p 159 (some 160)) = d65 p := by
  change d65 (change p 159 (some 160)) = d65 p
  exact sub1250 p
theorem sub1252 (p : Pattern) : d110 (change p 159 (some 160)) = d65 p := by
  change d109 (change p 159 (some 160)) = d65 p
  exact sub1251 p
theorem sub1253 (p : Pattern) : d336 (change p 159 (some 160)) = d66 p := by
  change (if p 141 then d110 (change p 159 (some 160)) else d107 (change p 159 (some 160))) = d66 p
  rw [sub1252, sub1249]
  rfl
theorem sub1254 (p : Pattern) : d337 (change p 159 (some 160)) = d1002 p := by
  change (if p 134 then d336 (change p 159 (some 160)) else d335 (change p 159 (some 160))) = d1002 p
  rw [sub1253, sub1247]
  rfl
theorem sub1255 (p : Pattern) : d338 (change p 159 (some 160)) = d456 p := by
  change (if p 158 then d55 (change p 159 (some 160)) else d114 (change p 159 (some 160))) = d456 p
  rw [sub1229, sub1232]
  rfl
theorem sub1256 (p : Pattern) : d339 (change p 159 (some 160)) = d457 p := by
  change (if p 158 then d65 (change p 159 (some 160)) else d116 (change p 159 (some 160))) = d457 p
  rw [sub1250, sub1246]
  rfl
theorem sub1257 (p : Pattern) : d340 (change p 159 (some 160)) = d458 p := by
  change (if p 141 then d339 (change p 159 (some 160)) else d338 (change p 159 (some 160))) = d458 p
  rw [sub1256, sub1255]
  rfl
theorem sub1258 (p : Pattern) : d211 (change p 159 (some 160)) = d55 p := by
  change (if p 158 then d55 (change p 159 (some 160)) else d107 (change p 159 (some 160))) = d55 p
  rw [sub1229, sub1249]
  simp only [ite_self]
theorem sub1259 (p : Pattern) : d212 (change p 159 (some 160)) = d65 p := by
  change (if p 158 then d65 (change p 159 (some 160)) else d110 (change p 159 (some 160))) = d65 p
  rw [sub1250, sub1252]
  simp only [ite_self]
theorem sub1260 (p : Pattern) : d213 (change p 159 (some 160)) = d66 p := by
  change (if p 141 then d212 (change p 159 (some 160)) else d211 (change p 159 (some 160))) = d66 p
  rw [sub1259, sub1258]
  rfl
theorem sub1261 (p : Pattern) : d341 (change p 159 (some 160)) = d1003 p := by
  change (if p 134 then d213 (change p 159 (some 160)) else d340 (change p 159 (some 160))) = d1003 p
  rw [sub1260, sub1257]
  rfl
theorem sub1262 (p : Pattern) : d342 (change p 159 (some 160)) = d1004 p := by
  change (if p 133 then d341 (change p 159 (some 160)) else d337 (change p 159 (some 160))) = d1004 p
  rw [sub1261, sub1254]
  rfl
theorem sub1263 (p : Pattern) : d66 (change p 159 (some 160)) = d66 p := by
  change (if p 141 then d65 (change p 159 (some 160)) else d55 (change p 159 (some 160))) = d66 p
  rw [sub1250, sub1229]
  rfl
theorem sub1264 (p : Pattern) : d343 (change p 159 (some 160)) = d1005 p := by
  change (if p 133 then d66 (change p 159 (some 160)) else d341 (change p 159 (some 160))) = d1005 p
  rw [sub1263, sub1261]
  rfl
theorem sub1265 (p : Pattern) : d344 (change p 159 (some 160)) = d1006 p := by
  change (if p 132 then d343 (change p 159 (some 160)) else d342 (change p 159 (some 160))) = d1006 p
  rw [sub1264, sub1262]
  rfl
theorem sub1266 (p : Pattern) : d345 (change p 159 (some 160)) = d1002 p := by
  change (if p 134 then d66 (change p 159 (some 160)) else d335 (change p 159 (some 160))) = d1002 p
  rw [sub1263, sub1247]
  rfl
theorem sub1267 (p : Pattern) : d119 (change p 159 (some 160)) = d119 p := by
  change (if p 187 then d55 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d119 p
  rw [sub1229, sub1226]
  rfl
theorem sub1268 (p : Pattern) : d137 (change p 159 (some 160)) = d137 p := by
  change (if p 186 then d55 (change p 159 (some 160)) else d119 (change p 159 (some 160))) = d137 p
  rw [sub1229, sub1267]
  rfl
theorem sub1269 (p : Pattern) : d138 (change p 159 (some 160)) = d137 p := by
  change d137 (change p 159 (some 160)) = d137 p
  exact sub1268 p
theorem sub1270 (p : Pattern) : d346 (change p 159 (some 160)) = d137 p := by
  change d138 (change p 159 (some 160)) = d137 p
  exact sub1269 p
theorem sub1271 (p : Pattern) : d347 (change p 159 (some 160)) = d1007 p := by
  change (if p 158 then d55 (change p 159 (some 160)) else d346 (change p 159 (some 160))) = d1007 p
  rw [sub1229, sub1270]
  rfl
theorem sub1272 (p : Pattern) : d125 (change p 159 (some 160)) = d125 p := by
  change (if p 187 then d60 (change p 159 (some 160)) else d11 (change p 159 (some 160))) = d125 p
  rw [sub1242, sub1238]
  rfl
theorem sub1273 (p : Pattern) : d143 (change p 159 (some 160)) = d143 p := by
  change (if p 186 then d60 (change p 159 (some 160)) else d125 (change p 159 (some 160))) = d143 p
  rw [sub1242, sub1272]
  rfl
theorem sub1274 (p : Pattern) : d144 (change p 159 (some 160)) = d144 p := by
  change (if p 168 then d143 (change p 159 (some 160)) else d137 (change p 159 (some 160))) = d144 p
  rw [sub1273, sub1268]
  rfl
theorem sub1275 (p : Pattern) : d145 (change p 159 (some 160)) = d144 p := by
  change d144 (change p 159 (some 160)) = d144 p
  exact sub1274 p
theorem sub1276 (p : Pattern) : d348 (change p 159 (some 160)) = d144 p := by
  change d145 (change p 159 (some 160)) = d144 p
  exact sub1275 p
theorem sub1277 (p : Pattern) : d349 (change p 159 (some 160)) = d1008 p := by
  change (if p 158 then d65 (change p 159 (some 160)) else d348 (change p 159 (some 160))) = d1008 p
  rw [sub1250, sub1276]
  rfl
theorem sub1278 (p : Pattern) : d350 (change p 159 (some 160)) = d1009 p := by
  change (if p 141 then d349 (change p 159 (some 160)) else d347 (change p 159 (some 160))) = d1009 p
  rw [sub1277, sub1271]
  rfl
theorem sub1279 (p : Pattern) : d351 (change p 159 (some 160)) = d1010 p := by
  change (if p 134 then d66 (change p 159 (some 160)) else d350 (change p 159 (some 160))) = d1010 p
  rw [sub1263, sub1278]
  rfl
theorem sub1280 (p : Pattern) : d352 (change p 159 (some 160)) = d1011 p := by
  change (if p 133 then d351 (change p 159 (some 160)) else d345 (change p 159 (some 160))) = d1011 p
  rw [sub1279, sub1266]
  rfl
theorem sub1281 (p : Pattern) : d353 (change p 159 (some 160)) = d1003 p := by
  change (if p 134 then d66 (change p 159 (some 160)) else d340 (change p 159 (some 160))) = d1003 p
  rw [sub1263, sub1257]
  rfl
theorem sub1282 (p : Pattern) : d354 (change p 159 (some 160)) = d1005 p := by
  change (if p 133 then d66 (change p 159 (some 160)) else d353 (change p 159 (some 160))) = d1005 p
  rw [sub1263, sub1281]
  rfl
theorem sub1283 (p : Pattern) : d355 (change p 159 (some 160)) = d1012 p := by
  change (if p 132 then d354 (change p 159 (some 160)) else d352 (change p 159 (some 160))) = d1012 p
  rw [sub1282, sub1280]
  rfl
theorem sub1284 (p : Pattern) : d356 (change p 159 (some 160)) = d1013 p := by
  change (if p 108 then d355 (change p 159 (some 160)) else d344 (change p 159 (some 160))) = d1013 p
  rw [sub1283, sub1265]
  rfl
theorem sub1285 (p : Pattern) : d0 (change p 160 none) = d0 p := by
  rfl
theorem sub1286 (p : Pattern) : d2 (change p 160 none) = d2 p := by
  rfl
theorem sub1287 (p : Pattern) : d6 (change p 160 none) = d6 p := by
  change (if p 193 then d2 (change p 160 none) else d0 (change p 160 none)) = d6 p
  rw [sub1286, sub1285]
  rfl
theorem sub1288 (p : Pattern) : d7 (change p 160 none) = d7 p := by
  change (if p 192 then d6 (change p 160 none) else d0 (change p 160 none)) = d7 p
  rw [sub1287, sub1285]
  rfl
theorem sub1289 (p : Pattern) : d106 (change p 160 none) = d7 p := by
  change d7 (change p 160 none) = d7 p
  exact sub1288 p
theorem sub1290 (p : Pattern) : d1 (change p 160 none) = d1 p := by
  rfl
theorem sub1291 (p : Pattern) : d8 (change p 160 none) = d8 p := by
  change (if p 271 then d1 (change p 160 none) else d0 (change p 160 none)) = d8 p
  rw [sub1290, sub1285]
  rfl
theorem sub1292 (p : Pattern) : d3 (change p 160 none) = d3 p := by
  rfl
theorem sub1293 (p : Pattern) : d9 (change p 160 none) = d9 p := by
  change (if p 271 then d3 (change p 160 none) else d2 (change p 160 none)) = d9 p
  rw [sub1292, sub1286]
  rfl
theorem sub1294 (p : Pattern) : d10 (change p 160 none) = d10 p := by
  change (if p 193 then d9 (change p 160 none) else d8 (change p 160 none)) = d10 p
  rw [sub1293, sub1291]
  rfl
theorem sub1295 (p : Pattern) : d11 (change p 160 none) = d11 p := by
  change (if p 192 then d10 (change p 160 none) else d8 (change p 160 none)) = d11 p
  rw [sub1294, sub1291]
  rfl
theorem sub1296 (p : Pattern) : d12 (change p 160 none) = d12 p := by
  change (if p 168 then d11 (change p 160 none) else d7 (change p 160 none)) = d12 p
  rw [sub1295, sub1288]
  rfl
theorem sub1297 (p : Pattern) : d109 (change p 160 none) = d12 p := by
  change d12 (change p 160 none) = d12 p
  exact sub1296 p
theorem sub1298 (p : Pattern) : d227 (change p 160 none) = d13 p := by
  change (if p 141 then d109 (change p 160 none) else d106 (change p 160 none)) = d13 p
  rw [sub1297, sub1289]
  rfl
theorem sub1299 (p : Pattern) : d4 (change p 160 none) = d4 p := by
  rfl
theorem sub1300 (p : Pattern) : d54 (change p 160 none) = d54 p := by
  change (if p 193 then d4 (change p 160 none) else d2 (change p 160 none)) = d54 p
  rw [sub1299, sub1286]
  rfl
theorem sub1301 (p : Pattern) : d55 (change p 160 none) = d55 p := by
  change (if p 192 then d54 (change p 160 none) else d2 (change p 160 none)) = d55 p
  rw [sub1300, sub1286]
  rfl
theorem sub1302 (p : Pattern) : d229 (change p 160 none) = d832 p := by
  change (if p 158 then d55 (change p 160 none) else d106 (change p 160 none)) = d832 p
  rw [sub1301, sub1289]
  rfl
theorem sub1303 (p : Pattern) : d5 (change p 160 none) = d5 p := by
  rfl
theorem sub1304 (p : Pattern) : d58 (change p 160 none) = d58 p := by
  change (if p 271 then d5 (change p 160 none) else d4 (change p 160 none)) = d58 p
  rw [sub1303, sub1299]
  rfl
theorem sub1305 (p : Pattern) : d59 (change p 160 none) = d59 p := by
  change (if p 193 then d58 (change p 160 none) else d9 (change p 160 none)) = d59 p
  rw [sub1304, sub1293]
  rfl
theorem sub1306 (p : Pattern) : d60 (change p 160 none) = d60 p := by
  change (if p 192 then d59 (change p 160 none) else d9 (change p 160 none)) = d60 p
  rw [sub1305, sub1293]
  rfl
theorem sub1307 (p : Pattern) : d65 (change p 160 none) = d65 p := by
  change (if p 168 then d60 (change p 160 none) else d55 (change p 160 none)) = d65 p
  rw [sub1306, sub1301]
  rfl
theorem sub1308 (p : Pattern) : d230 (change p 160 none) = d833 p := by
  change (if p 158 then d65 (change p 160 none) else d109 (change p 160 none)) = d833 p
  rw [sub1307, sub1297]
  rfl
theorem sub1309 (p : Pattern) : d231 (change p 160 none) = d834 p := by
  change (if p 141 then d230 (change p 160 none) else d229 (change p 160 none)) = d834 p
  rw [sub1308, sub1302]
  rfl
theorem sub1310 (p : Pattern) : d366 (change p 160 none) = d835 p := by
  change (if p 133 then d231 (change p 160 none) else d227 (change p 160 none)) = d835 p
  rw [sub1309, sub1298]
  rfl
theorem sub1311 (p : Pattern) : d66 (change p 160 none) = d66 p := by
  change (if p 141 then d65 (change p 160 none) else d55 (change p 160 none)) = d66 p
  rw [sub1307, sub1301]
  rfl
theorem sub1312 (p : Pattern) : d367 (change p 160 none) = d836 p := by
  change (if p 133 then d66 (change p 160 none) else d231 (change p 160 none)) = d836 p
  rw [sub1311, sub1309]
  rfl
theorem sub1313 (p : Pattern) : d368 (change p 160 none) = d837 p := by
  change (if p 132 then d367 (change p 160 none) else d366 (change p 160 none)) = d837 p
  rw [sub1312, sub1310]
  rfl
theorem sub1314 (p : Pattern) : d369 (change p 160 none) = d838 p := by
  change (if p 134 then d66 (change p 160 none) else d227 (change p 160 none)) = d838 p
  rw [sub1311, sub1298]
  rfl
theorem sub1315 (p : Pattern) : d370 (change p 160 none) = d839 p := by
  change (if p 134 then d66 (change p 160 none) else d231 (change p 160 none)) = d839 p
  rw [sub1311, sub1309]
  rfl
theorem sub1316 (p : Pattern) : d371 (change p 160 none) = d840 p := by
  change (if p 133 then d370 (change p 160 none) else d369 (change p 160 none)) = d840 p
  rw [sub1315, sub1314]
  rfl
theorem sub1317 (p : Pattern) : d372 (change p 160 none) = d841 p := by
  change (if p 133 then d66 (change p 160 none) else d370 (change p 160 none)) = d841 p
  rw [sub1311, sub1315]
  rfl
theorem sub1318 (p : Pattern) : d373 (change p 160 none) = d842 p := by
  change (if p 132 then d372 (change p 160 none) else d371 (change p 160 none)) = d842 p
  rw [sub1317, sub1316]
  rfl
theorem sub1319 (p : Pattern) : d374 (change p 160 none) = d843 p := by
  change (if p 108 then d373 (change p 160 none) else d368 (change p 160 none)) = d843 p
  rw [sub1318, sub1313]
  rfl
end NetHack.Sokoban12CostPartition
