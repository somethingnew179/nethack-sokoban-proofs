/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1200 (p : Pattern) : d237 (change p 113 none) = d1077 p := by
  change (if p 112 then d236 (change p 113 none) else d235 (change p 113 none)) = d1077 p
  rw [sub1199, sub1192]
  rfl
theorem sub1201 (p : Pattern) : d76 (change p 113 none) = d76 p := by
  change (if p 133 then d75 (change p 113 none) else d27 (change p 113 none)) = d76 p
  rw [sub1186, sub1150]
  rfl
theorem sub1202 (p : Pattern) : d77 (change p 113 none) = d77 p := by
  change (if p 132 then d76 (change p 113 none) else d28 (change p 113 none)) = d77 p
  rw [sub1201, sub1151]
  rfl
theorem sub1203 (p : Pattern) : d238 (change p 113 none) = d77 p := by
  change d77 (change p 113 none) = d77 p
  exact sub1202 p
theorem sub1204 (p : Pattern) : d107 (change p 113 none) = d107 p := by
  change (if p 133 then d2 (change p 113 none) else d99 (change p 113 none)) = d107 p
  rw [sub1124, sub1195]
  rfl
theorem sub1205 (p : Pattern) : d108 (change p 113 none) = d108 p := by
  change (if p 132 then d107 (change p 113 none) else d100 (change p 113 none)) = d108 p
  rw [sub1204, sub1196]
  rfl
theorem sub1206 (p : Pattern) : d239 (change p 113 none) = d108 p := by
  change d108 (change p 113 none) = d108 p
  exact sub1205 p
theorem sub1207 (p : Pattern) : d240 (change p 113 none) = d1078 p := by
  change (if p 112 then d239 (change p 113 none) else d238 (change p 113 none)) = d1078 p
  rw [sub1206, sub1203]
  rfl
theorem sub1208 (p : Pattern) : d241 (change p 113 none) = d1079 p := by
  change (if p 106 then d240 (change p 113 none) else d237 (change p 113 none)) = d1079 p
  rw [sub1207, sub1200]
  rfl
theorem sub1209 (p : Pattern) : d242 (change p 113 none) = d1080 p := by
  change (if p 86 then d241 (change p 113 none) else d234 (change p 113 none)) = d1080 p
  rw [sub1208, sub1191]
  rfl
theorem sub1210 (p : Pattern) : d243 (change p 113 none) = d51 p := by
  change d51 (change p 113 none) = d51 p
  exact sub1175 p
theorem sub1211 (p : Pattern) : d244 (change p 113 none) = d1074 p := by
  change (if p 112 then d243 (change p 113 none) else d235 (change p 113 none)) = d1074 p
  rw [sub1210, sub1192]
  rfl
theorem sub1212 (p : Pattern) : d245 (change p 113 none) = d80 p := by
  change d80 (change p 113 none) = d80 p
  exact sub1188 p
theorem sub1213 (p : Pattern) : d246 (change p 113 none) = d1081 p := by
  change (if p 112 then d245 (change p 113 none) else d238 (change p 113 none)) = d1081 p
  rw [sub1212, sub1203]
  rfl
theorem sub1214 (p : Pattern) : d247 (change p 113 none) = d1082 p := by
  change (if p 106 then d246 (change p 113 none) else d244 (change p 113 none)) = d1082 p
  rw [sub1213, sub1211]
  rfl
theorem sub1215 (p : Pattern) : d248 (change p 113 none) = d45 p := by
  change d45 (change p 113 none) = d45 p
  exact sub1168 p
theorem sub1216 (p : Pattern) : d249 (change p 113 none) = d102 p := by
  change d102 (change p 113 none) = d102 p
  exact sub1198 p
theorem sub1217 (p : Pattern) : d250 (change p 113 none) = d1077 p := by
  change (if p 112 then d249 (change p 113 none) else d248 (change p 113 none)) = d1077 p
  rw [sub1216, sub1215]
  rfl
theorem sub1218 (p : Pattern) : d251 (change p 113 none) = d77 p := by
  change d77 (change p 113 none) = d77 p
  exact sub1202 p
theorem sub1219 (p : Pattern) : d109 (change p 113 none) = d109 p := by
  change (if p 134 then d70 (change p 113 none) else d97 (change p 113 none)) = d109 p
  rw [sub1180, sub1193]
  rfl
theorem sub1220 (p : Pattern) : d110 (change p 113 none) = d110 p := by
  change (if p 133 then d109 (change p 113 none) else d97 (change p 113 none)) = d110 p
  rw [sub1219, sub1193]
  rfl
theorem sub1221 (p : Pattern) : d111 (change p 113 none) = d111 p := by
  change (if p 133 then d2 (change p 113 none) else d109 (change p 113 none)) = d111 p
  rw [sub1124, sub1219]
  rfl
theorem sub1222 (p : Pattern) : d112 (change p 113 none) = d112 p := by
  change (if p 132 then d111 (change p 113 none) else d110 (change p 113 none)) = d112 p
  rw [sub1221, sub1220]
  rfl
theorem sub1223 (p : Pattern) : d130 (change p 113 none) = d112 p := by
  change d112 (change p 113 none) = d112 p
  exact sub1222 p
theorem sub1224 (p : Pattern) : d252 (change p 113 none) = d1083 p := by
  change (if p 112 then d130 (change p 113 none) else d251 (change p 113 none)) = d1083 p
  rw [sub1223, sub1218]
  rfl
theorem sub1225 (p : Pattern) : d253 (change p 113 none) = d1084 p := by
  change (if p 106 then d252 (change p 113 none) else d250 (change p 113 none)) = d1084 p
  rw [sub1224, sub1217]
  rfl
theorem sub1226 (p : Pattern) : d254 (change p 113 none) = d1085 p := by
  change (if p 86 then d253 (change p 113 none) else d247 (change p 113 none)) = d1085 p
  rw [sub1225, sub1214]
  rfl
theorem sub1227 (p : Pattern) : d255 (change p 113 none) = d1086 p := by
  change (if p 80 then d254 (change p 113 none) else d242 (change p 113 none)) = d1086 p
  rw [sub1226, sub1209]
  rfl
theorem sub1228 (p : Pattern) : d0 (change p 139 none) = d0 p := by
  rfl
theorem sub1229 (p : Pattern) : d2 (change p 139 none) = d2 p := by
  rfl
theorem sub1230 (p : Pattern) : d3 (change p 139 none) = d3 p := by
  change (if p 161 then d2 (change p 139 none) else d0 (change p 139 none)) = d3 p
  rw [sub1229, sub1228]
  rfl
theorem sub1231 (p : Pattern) : d4 (change p 139 none) = d4 p := by
  change (if p 160 then d3 (change p 139 none) else d0 (change p 139 none)) = d4 p
  rw [sub1230, sub1228]
  rfl
theorem sub1232 (p : Pattern) : d5 (change p 139 none) = d5 p := by
  change (if p 160 then d2 (change p 139 none) else d0 (change p 139 none)) = d5 p
  rw [sub1229, sub1228]
  rfl
theorem sub1233 (p : Pattern) : d6 (change p 139 none) = d6 p := by
  change (if p 159 then d5 (change p 139 none) else d4 (change p 139 none)) = d6 p
  rw [sub1232, sub1231]
  rfl
theorem sub1234 (p : Pattern) : d7 (change p 139 none) = d7 p := by
  change (if p 159 then d2 (change p 139 none) else d4 (change p 139 none)) = d7 p
  rw [sub1229, sub1231]
  rfl
theorem sub1235 (p : Pattern) : d8 (change p 139 none) = d8 p := by
  change (if p 158 then d7 (change p 139 none) else d6 (change p 139 none)) = d8 p
  rw [sub1234, sub1233]
  rfl
theorem sub1236 (p : Pattern) : d456 (change p 139 none) = d8 p := by
  change d8 (change p 139 none) = d8 p
  exact sub1235 p
theorem sub1237 (p : Pattern) : d52 (change p 139 none) = d8 p := by
  change d8 (change p 139 none) = d8 p
  exact sub1235 p
theorem sub1238 (p : Pattern) : d457 (change p 139 none) = d8 p := by
  change (if p 138 then d52 (change p 139 none) else d456 (change p 139 none)) = d8 p
  rw [sub1237, sub1236]
  simp only [ite_self]
theorem sub1239 (p : Pattern) : d458 (change p 139 none) = d8 p := by
  change (if p 134 then d52 (change p 139 none) else d457 (change p 139 none)) = d8 p
  rw [sub1237, sub1238]
  simp only [ite_self]
theorem sub1240 (p : Pattern) : d459 (change p 139 none) = d8 p := by
  change d8 (change p 139 none) = d8 p
  exact sub1235 p
theorem sub1241 (p : Pattern) : d460 (change p 139 none) = d8 p := by
  change (if p 138 then d52 (change p 139 none) else d459 (change p 139 none)) = d8 p
  rw [sub1237, sub1240]
  simp only [ite_self]
theorem sub1242 (p : Pattern) : d17 (change p 139 none) = d17 p := by
  change (if p 160 then d2 (change p 139 none) else d3 (change p 139 none)) = d17 p
  rw [sub1229, sub1230]
  rfl
theorem sub1243 (p : Pattern) : d18 (change p 139 none) = d18 p := by
  change (if p 159 then d17 (change p 139 none) else d4 (change p 139 none)) = d18 p
  rw [sub1242, sub1231]
  rfl
theorem sub1244 (p : Pattern) : d19 (change p 139 none) = d19 p := by
  change (if p 159 then d2 (change p 139 none) else d17 (change p 139 none)) = d19 p
  rw [sub1229, sub1242]
  rfl
theorem sub1245 (p : Pattern) : d20 (change p 139 none) = d20 p := by
  change (if p 158 then d19 (change p 139 none) else d18 (change p 139 none)) = d20 p
  rw [sub1244, sub1243]
  rfl
theorem sub1246 (p : Pattern) : d54 (change p 139 none) = d20 p := by
  change d20 (change p 139 none) = d20 p
  exact sub1245 p
theorem sub1247 (p : Pattern) : d461 (change p 139 none) = d1097 p := by
  change (if p 134 then d54 (change p 139 none) else d460 (change p 139 none)) = d1097 p
  rw [sub1246, sub1241]
  rfl
theorem sub1248 (p : Pattern) : d462 (change p 139 none) = d1098 p := by
  change (if p 133 then d461 (change p 139 none) else d458 (change p 139 none)) = d1098 p
  rw [sub1247, sub1239]
  rfl
theorem sub1249 (p : Pattern) : d1 (change p 139 none) = d1 p := by
  rfl
theorem sub1250 (p : Pattern) : d29 (change p 139 none) = d29 p := by
  change (if p 161 then d1 (change p 139 none) else d0 (change p 139 none)) = d29 p
  rw [sub1249, sub1228]
  rfl
theorem sub1251 (p : Pattern) : d30 (change p 139 none) = d30 p := by
  change (if p 160 then d2 (change p 139 none) else d29 (change p 139 none)) = d30 p
  rw [sub1229, sub1250]
  rfl
theorem sub1252 (p : Pattern) : d31 (change p 139 none) = d31 p := by
  change (if p 159 then d30 (change p 139 none) else d4 (change p 139 none)) = d31 p
  rw [sub1251, sub1231]
  rfl
theorem sub1253 (p : Pattern) : d32 (change p 139 none) = d32 p := by
  change (if p 159 then d2 (change p 139 none) else d30 (change p 139 none)) = d32 p
  rw [sub1229, sub1251]
  rfl
theorem sub1254 (p : Pattern) : d33 (change p 139 none) = d33 p := by
  change (if p 158 then d32 (change p 139 none) else d31 (change p 139 none)) = d33 p
  rw [sub1253, sub1252]
  rfl
theorem sub1255 (p : Pattern) : d58 (change p 139 none) = d33 p := by
  change d33 (change p 139 none) = d33 p
  exact sub1254 p
theorem sub1256 (p : Pattern) : d463 (change p 139 none) = d1099 p := by
  change (if p 134 then d58 (change p 139 none) else d457 (change p 139 none)) = d1099 p
  rw [sub1255, sub1238]
  rfl
theorem sub1257 (p : Pattern) : d37 (change p 139 none) = d37 p := by
  change (if p 159 then d2 (change p 139 none) else d5 (change p 139 none)) = d37 p
  rw [sub1229, sub1232]
  rfl
theorem sub1258 (p : Pattern) : d38 (change p 139 none) = d38 p := by
  change (if p 158 then d37 (change p 139 none) else d6 (change p 139 none)) = d38 p
  rw [sub1257, sub1233]
  rfl
theorem sub1259 (p : Pattern) : d464 (change p 139 none) = d38 p := by
  change d38 (change p 139 none) = d38 p
  exact sub1258 p
theorem sub1260 (p : Pattern) : d61 (change p 139 none) = d38 p := by
  change d38 (change p 139 none) = d38 p
  exact sub1258 p
theorem sub1261 (p : Pattern) : d465 (change p 139 none) = d38 p := by
  change (if p 138 then d61 (change p 139 none) else d464 (change p 139 none)) = d38 p
  rw [sub1260, sub1259]
  simp only [ite_self]
theorem sub1262 (p : Pattern) : d466 (change p 139 none) = d1100 p := by
  change (if p 134 then d54 (change p 139 none) else d465 (change p 139 none)) = d1100 p
  rw [sub1246, sub1261]
  rfl
theorem sub1263 (p : Pattern) : d467 (change p 139 none) = d1101 p := by
  change (if p 133 then d466 (change p 139 none) else d463 (change p 139 none)) = d1101 p
  rw [sub1262, sub1256]
  rfl
theorem sub1264 (p : Pattern) : d468 (change p 139 none) = d1102 p := by
  change (if p 132 then d467 (change p 139 none) else d462 (change p 139 none)) = d1102 p
  rw [sub1263, sub1248]
  rfl
theorem sub1265 (p : Pattern) : d469 (change p 139 none) = d8 p := by
  change (if p 134 then d52 (change p 139 none) else d460 (change p 139 none)) = d8 p
  rw [sub1237, sub1241]
  simp only [ite_self]
theorem sub1266 (p : Pattern) : d470 (change p 139 none) = d1097 p := by
  change (if p 134 then d54 (change p 139 none) else d52 (change p 139 none)) = d1097 p
  rw [sub1246, sub1237]
  rfl
theorem sub1267 (p : Pattern) : d471 (change p 139 none) = d1098 p := by
  change (if p 133 then d470 (change p 139 none) else d469 (change p 139 none)) = d1098 p
  rw [sub1266, sub1265]
  rfl
theorem sub1268 (p : Pattern) : d472 (change p 139 none) = d1099 p := by
  change (if p 134 then d58 (change p 139 none) else d460 (change p 139 none)) = d1099 p
  rw [sub1255, sub1241]
  rfl
theorem sub1269 (p : Pattern) : d473 (change p 139 none) = d1100 p := by
  change (if p 134 then d54 (change p 139 none) else d61 (change p 139 none)) = d1100 p
  rw [sub1246, sub1260]
  rfl
theorem sub1270 (p : Pattern) : d474 (change p 139 none) = d1101 p := by
  change (if p 133 then d473 (change p 139 none) else d472 (change p 139 none)) = d1101 p
  rw [sub1269, sub1268]
  rfl
theorem sub1271 (p : Pattern) : d475 (change p 139 none) = d1102 p := by
  change (if p 132 then d474 (change p 139 none) else d471 (change p 139 none)) = d1102 p
  rw [sub1270, sub1267]
  rfl
theorem sub1272 (p : Pattern) : d476 (change p 139 none) = d1102 p := by
  change (if p 112 then d475 (change p 139 none) else d468 (change p 139 none)) = d1102 p
  rw [sub1271, sub1264]
  simp only [ite_self]
theorem sub1273 (p : Pattern) : d477 (change p 139 none) = d1097 p := by
  change (if p 134 then d54 (change p 139 none) else d457 (change p 139 none)) = d1097 p
  rw [sub1246, sub1238]
  rfl
theorem sub1274 (p : Pattern) : d9 (change p 139 none) = d9 p := by
  change (if p 161 then d2 (change p 139 none) else d1 (change p 139 none)) = d9 p
  rw [sub1229, sub1249]
  rfl
theorem sub1275 (p : Pattern) : d10 (change p 139 none) = d10 p := by
  change (if p 160 then d9 (change p 139 none) else d1 (change p 139 none)) = d10 p
  rw [sub1274, sub1249]
  rfl
theorem sub1276 (p : Pattern) : d11 (change p 139 none) = d11 p := by
  change (if p 160 then d2 (change p 139 none) else d1 (change p 139 none)) = d11 p
  rw [sub1229, sub1249]
  rfl
theorem sub1277 (p : Pattern) : d12 (change p 139 none) = d12 p := by
  change (if p 159 then d11 (change p 139 none) else d10 (change p 139 none)) = d12 p
  rw [sub1276, sub1275]
  rfl
theorem sub1278 (p : Pattern) : d39 (change p 139 none) = d39 p := by
  change (if p 159 then d2 (change p 139 none) else d11 (change p 139 none)) = d39 p
  rw [sub1229, sub1276]
  rfl
theorem sub1279 (p : Pattern) : d40 (change p 139 none) = d40 p := by
  change (if p 158 then d39 (change p 139 none) else d12 (change p 139 none)) = d40 p
  rw [sub1278, sub1277]
  rfl
theorem sub1280 (p : Pattern) : d478 (change p 139 none) = d40 p := by
  change d40 (change p 139 none) = d40 p
  exact sub1279 p
theorem sub1281 (p : Pattern) : d68 (change p 139 none) = d40 p := by
  change d40 (change p 139 none) = d40 p
  exact sub1279 p
theorem sub1282 (p : Pattern) : d479 (change p 139 none) = d40 p := by
  change (if p 138 then d68 (change p 139 none) else d478 (change p 139 none)) = d40 p
  rw [sub1281, sub1280]
  simp only [ite_self]
theorem sub1283 (p : Pattern) : d21 (change p 139 none) = d21 p := by
  change (if p 160 then d2 (change p 139 none) else d9 (change p 139 none)) = d21 p
  rw [sub1229, sub1274]
  rfl
theorem sub1284 (p : Pattern) : d22 (change p 139 none) = d22 p := by
  change (if p 159 then d21 (change p 139 none) else d10 (change p 139 none)) = d22 p
  rw [sub1283, sub1275]
  rfl
theorem sub1285 (p : Pattern) : d23 (change p 139 none) = d23 p := by
  change (if p 159 then d2 (change p 139 none) else d21 (change p 139 none)) = d23 p
  rw [sub1229, sub1283]
  rfl
theorem sub1286 (p : Pattern) : d24 (change p 139 none) = d24 p := by
  change (if p 158 then d23 (change p 139 none) else d22 (change p 139 none)) = d24 p
  rw [sub1285, sub1284]
  rfl
theorem sub1287 (p : Pattern) : d70 (change p 139 none) = d24 p := by
  change d24 (change p 139 none) = d24 p
  exact sub1286 p
theorem sub1288 (p : Pattern) : d480 (change p 139 none) = d1103 p := by
  change (if p 134 then d70 (change p 139 none) else d479 (change p 139 none)) = d1103 p
  rw [sub1287, sub1282]
  rfl
theorem sub1289 (p : Pattern) : d481 (change p 139 none) = d1104 p := by
  change (if p 133 then d480 (change p 139 none) else d477 (change p 139 none)) = d1104 p
  rw [sub1288, sub1273]
  rfl
theorem sub1290 (p : Pattern) : d482 (change p 139 none) = d1105 p := by
  change (if p 132 then d481 (change p 139 none) else d462 (change p 139 none)) = d1105 p
  rw [sub1289, sub1248]
  rfl
theorem sub1291 (p : Pattern) : d483 (change p 139 none) = d8 p := by
  change d8 (change p 139 none) = d8 p
  exact sub1235 p
theorem sub1292 (p : Pattern) : d484 (change p 139 none) = d8 p := by
  change (if p 138 then d52 (change p 139 none) else d483 (change p 139 none)) = d8 p
  rw [sub1237, sub1291]
  simp only [ite_self]
theorem sub1293 (p : Pattern) : d485 (change p 139 none) = d1097 p := by
  change (if p 134 then d54 (change p 139 none) else d484 (change p 139 none)) = d1097 p
  rw [sub1246, sub1292]
  rfl
theorem sub1294 (p : Pattern) : d75 (change p 139 none) = d1103 p := by
  change (if p 134 then d70 (change p 139 none) else d68 (change p 139 none)) = d1103 p
  rw [sub1287, sub1281]
  rfl
theorem sub1295 (p : Pattern) : d486 (change p 139 none) = d1104 p := by
  change (if p 133 then d75 (change p 139 none) else d485 (change p 139 none)) = d1104 p
  rw [sub1294, sub1293]
  rfl
theorem sub1296 (p : Pattern) : d487 (change p 139 none) = d1105 p := by
  change (if p 132 then d486 (change p 139 none) else d462 (change p 139 none)) = d1105 p
  rw [sub1295, sub1248]
  rfl
theorem sub1297 (p : Pattern) : d488 (change p 139 none) = d1105 p := by
  change (if p 113 then d487 (change p 139 none) else d482 (change p 139 none)) = d1105 p
  rw [sub1296, sub1290]
  simp only [ite_self]
theorem sub1298 (p : Pattern) : d489 (change p 139 none) = d1104 p := by
  change (if p 133 then d75 (change p 139 none) else d461 (change p 139 none)) = d1104 p
  rw [sub1294, sub1247]
  rfl
theorem sub1299 (p : Pattern) : d490 (change p 139 none) = d1105 p := by
  change (if p 132 then d489 (change p 139 none) else d471 (change p 139 none)) = d1105 p
  rw [sub1298, sub1267]
  rfl
theorem sub1300 (p : Pattern) : d491 (change p 139 none) = d1104 p := by
  change (if p 133 then d75 (change p 139 none) else d470 (change p 139 none)) = d1104 p
  rw [sub1294, sub1266]
  rfl
theorem sub1301 (p : Pattern) : d492 (change p 139 none) = d1105 p := by
  change (if p 132 then d491 (change p 139 none) else d471 (change p 139 none)) = d1105 p
  rw [sub1300, sub1267]
  rfl
theorem sub1302 (p : Pattern) : d493 (change p 139 none) = d1105 p := by
  change (if p 113 then d492 (change p 139 none) else d490 (change p 139 none)) = d1105 p
  rw [sub1301, sub1299]
  simp only [ite_self]
theorem sub1303 (p : Pattern) : d494 (change p 139 none) = d1105 p := by
  change (if p 112 then d493 (change p 139 none) else d488 (change p 139 none)) = d1105 p
  rw [sub1302, sub1297]
  simp only [ite_self]
theorem sub1304 (p : Pattern) : d495 (change p 139 none) = d1106 p := by
  change (if p 106 then d494 (change p 139 none) else d476 (change p 139 none)) = d1106 p
  rw [sub1303, sub1272]
  rfl
theorem sub1305 (p : Pattern) : d496 (change p 139 none) = d1099 p := by
  change (if p 134 then d58 (change p 139 none) else d484 (change p 139 none)) = d1099 p
  rw [sub1255, sub1292]
  rfl
theorem sub1306 (p : Pattern) : d497 (change p 139 none) = d1101 p := by
  change (if p 133 then d473 (change p 139 none) else d496 (change p 139 none)) = d1101 p
  rw [sub1269, sub1305]
  rfl
theorem sub1307 (p : Pattern) : d498 (change p 139 none) = d1102 p := by
  change (if p 132 then d497 (change p 139 none) else d462 (change p 139 none)) = d1102 p
  rw [sub1306, sub1248]
  rfl
theorem sub1308 (p : Pattern) : d499 (change p 139 none) = d1102 p := by
  change (if p 113 then d498 (change p 139 none) else d468 (change p 139 none)) = d1102 p
  rw [sub1307, sub1264]
  simp only [ite_self]
theorem sub1309 (p : Pattern) : d13 (change p 139 none) = d13 p := by
  change (if p 159 then d2 (change p 139 none) else d10 (change p 139 none)) = d13 p
  rw [sub1229, sub1275]
  rfl
theorem sub1310 (p : Pattern) : d14 (change p 139 none) = d14 p := by
  change (if p 158 then d13 (change p 139 none) else d12 (change p 139 none)) = d14 p
  rw [sub1309, sub1277]
  rfl
theorem sub1311 (p : Pattern) : d500 (change p 139 none) = d14 p := by
  change d14 (change p 139 none) = d14 p
  exact sub1310 p
theorem sub1312 (p : Pattern) : d97 (change p 139 none) = d14 p := by
  change d14 (change p 139 none) = d14 p
  exact sub1310 p
theorem sub1313 (p : Pattern) : d501 (change p 139 none) = d14 p := by
  change (if p 138 then d97 (change p 139 none) else d500 (change p 139 none)) = d14 p
  rw [sub1312, sub1311]
  simp only [ite_self]
theorem sub1314 (p : Pattern) : d502 (change p 139 none) = d14 p := by
  change (if p 134 then d97 (change p 139 none) else d501 (change p 139 none)) = d14 p
  rw [sub1312, sub1313]
  simp only [ite_self]
theorem sub1315 (p : Pattern) : d109 (change p 139 none) = d1107 p := by
  change (if p 134 then d70 (change p 139 none) else d97 (change p 139 none)) = d1107 p
  rw [sub1287, sub1312]
  rfl
theorem sub1316 (p : Pattern) : d503 (change p 139 none) = d1108 p := by
  change (if p 133 then d109 (change p 139 none) else d502 (change p 139 none)) = d1108 p
  rw [sub1315, sub1314]
  rfl
theorem sub1317 (p : Pattern) : d504 (change p 139 none) = d1107 p := by
  change (if p 134 then d70 (change p 139 none) else d501 (change p 139 none)) = d1107 p
  rw [sub1287, sub1313]
  rfl
theorem sub1318 (p : Pattern) : d505 (change p 139 none) = d1109 p := by
  change (if p 133 then d75 (change p 139 none) else d504 (change p 139 none)) = d1109 p
  rw [sub1294, sub1317]
  rfl
theorem sub1319 (p : Pattern) : d506 (change p 139 none) = d1110 p := by
  change (if p 132 then d505 (change p 139 none) else d503 (change p 139 none)) = d1110 p
  rw [sub1318, sub1316]
  rfl
end NetHack.Sokoban32Refined
