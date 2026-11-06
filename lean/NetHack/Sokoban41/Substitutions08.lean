/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions07
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s1200 (pattern : Ten) : d209 (change pattern 5 10) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 5 10) else d205 (change pattern 5 10)) = d209 pattern
  rw [s1174, s1195]
  rfl
theorem s1201 (pattern : Ten) : d214 (change pattern 5 10) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 5 10) else d209 (change pattern 5 10)) = d214 pattern
  rw [s1174, s1200]
  rfl
theorem s1202 (pattern : Ten) : d217 (change pattern 5 10) = d217 pattern := by
  change (if pattern.c then d10 (change pattern 5 10) else d214 (change pattern 5 10)) = d217 pattern
  rw [s1174, s1201]
  rfl
theorem s1203 (pattern : Ten) : d299 (change pattern 5 10) = d299 pattern := by
  change (if pattern.e then d217 (change pattern 5 10) else d209 (change pattern 5 10)) = d299 pattern
  rw [s1202, s1200]
  rfl
theorem s1204 (pattern : Ten) : d300 (change pattern 5 10) = d566 pattern := by
  change (if pattern.d then d299 (change pattern 5 10) else d298 (change pattern 5 10)) = d566 pattern
  rw [s1203, s1199]
  rfl
theorem s1205 (pattern : Ten) : d0 (change pattern 6 4) = d0 pattern := by
  rfl
theorem s1206 (pattern : Ten) : d2 (change pattern 6 4) = d2 pattern := by
  rfl
theorem s1207 (pattern : Ten) : d15 (change pattern 6 4) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 6 4) else d0 (change pattern 6 4)) = d15 pattern
  rw [s1206, s1205]
  rfl
theorem s1208 (pattern : Ten) : d4 (change pattern 6 4) = d4 pattern := by
  rfl
theorem s1209 (pattern : Ten) : d10 (change pattern 6 4) = d10 pattern := by
  rfl
theorem s1210 (pattern : Ten) : d42 (change pattern 6 4) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d4 (change pattern 6 4)) = d42 pattern
  rw [s1209, s1208]
  rfl
theorem s1211 (pattern : Ten) : d48 (change pattern 6 4) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 6 4) else d15 (change pattern 6 4)) = d48 pattern
  rw [s1210, s1207]
  rfl
theorem s1212 (pattern : Ten) : d6 (change pattern 6 4) = d6 pattern := by
  rfl
theorem s1213 (pattern : Ten) : d43 (change pattern 6 4) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d6 (change pattern 6 4)) = d43 pattern
  rw [s1209, s1212]
  rfl
theorem s1214 (pattern : Ten) : d49 (change pattern 6 4) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d43 (change pattern 6 4)) = d49 pattern
  rw [s1209, s1213]
  rfl
theorem s1215 (pattern : Ten) : d54 (change pattern 6 4) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 6 4) else d48 (change pattern 6 4)) = d54 pattern
  rw [s1214, s1211]
  rfl
theorem s1216 (pattern : Ten) : d44 (change pattern 6 4) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 6 4) else d2 (change pattern 6 4)) = d44 pattern
  rw [s1208, s1206]
  rfl
theorem s1217 (pattern : Ten) : d50 (change pattern 6 4) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 6 4) else d44 (change pattern 6 4)) = d50 pattern
  rw [s1213, s1216]
  rfl
theorem s1218 (pattern : Ten) : d8 (change pattern 6 4) = d8 pattern := by
  rfl
theorem s1219 (pattern : Ten) : d45 (change pattern 6 4) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d8 (change pattern 6 4)) = d45 pattern
  rw [s1209, s1218]
  rfl
theorem s1220 (pattern : Ten) : d51 (change pattern 6 4) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d45 (change pattern 6 4)) = d51 pattern
  rw [s1209, s1219]
  rfl
theorem s1221 (pattern : Ten) : d55 (change pattern 6 4) = d55 pattern := by
  change (if pattern.h then d51 (change pattern 6 4) else d50 (change pattern 6 4)) = d55 pattern
  rw [s1220, s1217]
  rfl
theorem s1222 (pattern : Ten) : d152 (change pattern 6 4) = d152 pattern := by
  change (if pattern.c then d55 (change pattern 6 4) else d54 (change pattern 6 4)) = d152 pattern
  rw [s1221, s1215]
  rfl
theorem s1223 (pattern : Ten) : d154 (change pattern 6 4) = d152 pattern := by
  change d152 (change pattern 6 4) = d152 pattern
  exact s1222 pattern
theorem s1224 (pattern : Ten) : d7 (change pattern 6 4) = d7 pattern := by
  rfl
theorem s1225 (pattern : Ten) : d38 (change pattern 6 4) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 6 4) else d7 (change pattern 6 4)) = d38 pattern
  rw [s1218, s1224]
  rfl
theorem s1226 (pattern : Ten) : d40 (change pattern 6 4) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 6 4) else d38 (change pattern 6 4)) = d40 pattern
  rw [s1218, s1225]
  rfl
theorem s1227 (pattern : Ten) : d46 (change pattern 6 4) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d40 (change pattern 6 4)) = d46 pattern
  rw [s1209, s1226]
  rfl
theorem s1228 (pattern : Ten) : d52 (change pattern 6 4) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d46 (change pattern 6 4)) = d52 pattern
  rw [s1209, s1227]
  rfl
theorem s1229 (pattern : Ten) : d56 (change pattern 6 4) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 6 4) else d52 (change pattern 6 4)) = d56 pattern
  rw [s1209, s1228]
  rfl
theorem s1230 (pattern : Ten) : d9 (change pattern 6 4) = d9 pattern := by
  rfl
theorem s1231 (pattern : Ten) : d39 (change pattern 6 4) = d39 pattern := by
  change (if pattern.b then d10 (change pattern 6 4) else d9 (change pattern 6 4)) = d39 pattern
  rw [s1209, s1230]
  rfl
theorem s1232 (pattern : Ten) : d41 (change pattern 6 4) = d41 pattern := by
  change (if pattern.a then d10 (change pattern 6 4) else d39 (change pattern 6 4)) = d41 pattern
  rw [s1209, s1231]
  rfl
theorem s1233 (pattern : Ten) : d47 (change pattern 6 4) = d47 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d41 (change pattern 6 4)) = d47 pattern
  rw [s1209, s1232]
  rfl
theorem s1234 (pattern : Ten) : d53 (change pattern 6 4) = d53 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d47 (change pattern 6 4)) = d53 pattern
  rw [s1209, s1233]
  rfl
theorem s1235 (pattern : Ten) : d57 (change pattern 6 4) = d57 pattern := by
  change (if pattern.h then d10 (change pattern 6 4) else d53 (change pattern 6 4)) = d57 pattern
  rw [s1209, s1234]
  rfl
theorem s1236 (pattern : Ten) : d153 (change pattern 6 4) = d153 pattern := by
  change (if pattern.c then d57 (change pattern 6 4) else d56 (change pattern 6 4)) = d153 pattern
  rw [s1235, s1229]
  rfl
theorem s1237 (pattern : Ten) : d155 (change pattern 6 4) = d153 pattern := by
  change d153 (change pattern 6 4) = d153 pattern
  exact s1236 pattern
theorem s1238 (pattern : Ten) : d156 (change pattern 6 4) = d569 pattern := by
  change (if pattern.d then d155 (change pattern 6 4) else d154 (change pattern 6 4)) = d569 pattern
  rw [s1237, s1223]
  rfl
theorem s1239 (pattern : Ten) : d1 (change pattern 6 4) = d1 pattern := by
  rfl
theorem s1240 (pattern : Ten) : d171 (change pattern 6 4) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 6 4) else d0 (change pattern 6 4)) = d171 pattern
  rw [s1239, s1205]
  rfl
theorem s1241 (pattern : Ten) : d309 (change pattern 6 4) = d309 pattern := by
  change (if pattern.a then d2 (change pattern 6 4) else d1 (change pattern 6 4)) = d309 pattern
  rw [s1206, s1239]
  rfl
theorem s1242 (pattern : Ten) : d313 (change pattern 6 4) = d313 pattern := by
  change (if pattern.f then d309 (change pattern 6 4) else d171 (change pattern 6 4)) = d313 pattern
  rw [s1241, s1240]
  rfl
theorem s1243 (pattern : Ten) : d3 (change pattern 6 4) = d3 pattern := by
  rfl
theorem s1244 (pattern : Ten) : d172 (change pattern 6 4) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 6 4) else d2 (change pattern 6 4)) = d172 pattern
  rw [s1243, s1206]
  rfl
theorem s1245 (pattern : Ten) : d310 (change pattern 6 4) = d310 pattern := by
  change (if pattern.a then d4 (change pattern 6 4) else d3 (change pattern 6 4)) = d310 pattern
  rw [s1208, s1243]
  rfl
theorem s1246 (pattern : Ten) : d314 (change pattern 6 4) = d314 pattern := by
  change (if pattern.f then d310 (change pattern 6 4) else d172 (change pattern 6 4)) = d314 pattern
  rw [s1245, s1244]
  rfl
theorem s1247 (pattern : Ten) : d317 (change pattern 6 4) = d317 pattern := by
  change (if pattern.j then d314 (change pattern 6 4) else d313 (change pattern 6 4)) = d317 pattern
  rw [s1246, s1242]
  rfl
theorem s1248 (pattern : Ten) : d5 (change pattern 6 4) = d5 pattern := by
  rfl
theorem s1249 (pattern : Ten) : d193 (change pattern 6 4) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 6 4) else d4 (change pattern 6 4)) = d193 pattern
  rw [s1248, s1208]
  rfl
theorem s1250 (pattern : Ten) : d311 (change pattern 6 4) = d311 pattern := by
  change (if pattern.a then d6 (change pattern 6 4) else d5 (change pattern 6 4)) = d311 pattern
  rw [s1212, s1248]
  rfl
theorem s1251 (pattern : Ten) : d315 (change pattern 6 4) = d315 pattern := by
  change (if pattern.f then d311 (change pattern 6 4) else d193 (change pattern 6 4)) = d315 pattern
  rw [s1250, s1249]
  rfl
theorem s1252 (pattern : Ten) : d318 (change pattern 6 4) = d318 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d315 (change pattern 6 4)) = d318 pattern
  rw [s1209, s1251]
  rfl
theorem s1253 (pattern : Ten) : d321 (change pattern 6 4) = d321 pattern := by
  change (if pattern.i then d318 (change pattern 6 4) else d317 (change pattern 6 4)) = d321 pattern
  rw [s1252, s1247]
  rfl
theorem s1254 (pattern : Ten) : d194 (change pattern 6 4) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 6 4) else d6 (change pattern 6 4)) = d194 pattern
  rw [s1224, s1212]
  rfl
theorem s1255 (pattern : Ten) : d312 (change pattern 6 4) = d312 pattern := by
  change (if pattern.a then d8 (change pattern 6 4) else d7 (change pattern 6 4)) = d312 pattern
  rw [s1218, s1224]
  rfl
theorem s1256 (pattern : Ten) : d316 (change pattern 6 4) = d316 pattern := by
  change (if pattern.f then d312 (change pattern 6 4) else d194 (change pattern 6 4)) = d316 pattern
  rw [s1255, s1254]
  rfl
theorem s1257 (pattern : Ten) : d319 (change pattern 6 4) = d319 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d316 (change pattern 6 4)) = d319 pattern
  rw [s1209, s1256]
  rfl
theorem s1258 (pattern : Ten) : d322 (change pattern 6 4) = d322 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d319 (change pattern 6 4)) = d322 pattern
  rw [s1209, s1257]
  rfl
theorem s1259 (pattern : Ten) : d324 (change pattern 6 4) = d324 pattern := by
  change (if pattern.h then d322 (change pattern 6 4) else d321 (change pattern 6 4)) = d324 pattern
  rw [s1258, s1253]
  rfl
theorem s1260 (pattern : Ten) : d320 (change pattern 6 4) = d320 pattern := by
  change (if pattern.j then d315 (change pattern 6 4) else d314 (change pattern 6 4)) = d320 pattern
  rw [s1251, s1246]
  rfl
theorem s1261 (pattern : Ten) : d323 (change pattern 6 4) = d323 pattern := by
  change (if pattern.i then d319 (change pattern 6 4) else d320 (change pattern 6 4)) = d323 pattern
  rw [s1257, s1260]
  rfl
theorem s1262 (pattern : Ten) : d195 (change pattern 6 4) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 6 4) else d8 (change pattern 6 4)) = d195 pattern
  rw [s1230, s1218]
  rfl
theorem s1263 (pattern : Ten) : d11 (change pattern 6 4) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 6 4) else d9 (change pattern 6 4)) = d11 pattern
  rw [s1209, s1230]
  rfl
theorem s1264 (pattern : Ten) : d196 (change pattern 6 4) = d196 pattern := by
  change (if pattern.f then d11 (change pattern 6 4) else d195 (change pattern 6 4)) = d196 pattern
  rw [s1263, s1262]
  rfl
theorem s1265 (pattern : Ten) : d201 (change pattern 6 4) = d201 pattern := by
  change (if pattern.j then d10 (change pattern 6 4) else d196 (change pattern 6 4)) = d201 pattern
  rw [s1209, s1264]
  rfl
theorem s1266 (pattern : Ten) : d206 (change pattern 6 4) = d206 pattern := by
  change (if pattern.i then d10 (change pattern 6 4) else d201 (change pattern 6 4)) = d206 pattern
  rw [s1209, s1265]
  rfl
theorem s1267 (pattern : Ten) : d325 (change pattern 6 4) = d325 pattern := by
  change (if pattern.h then d206 (change pattern 6 4) else d323 (change pattern 6 4)) = d325 pattern
  rw [s1266, s1261]
  rfl
theorem s1268 (pattern : Ten) : d327 (change pattern 6 4) = d327 pattern := by
  change (if pattern.c then d325 (change pattern 6 4) else d324 (change pattern 6 4)) = d327 pattern
  rw [s1267, s1259]
  rfl
theorem s1269 (pattern : Ten) : d329 (change pattern 6 4) = d327 pattern := by
  change d327 (change pattern 6 4) = d327 pattern
  exact s1268 pattern
theorem s1270 (pattern : Ten) : d210 (change pattern 6 4) = d210 pattern := by
  change (if pattern.h then d10 (change pattern 6 4) else d206 (change pattern 6 4)) = d210 pattern
  rw [s1209, s1266]
  rfl
theorem s1271 (pattern : Ten) : d328 (change pattern 6 4) = d328 pattern := by
  change (if pattern.c then d10 (change pattern 6 4) else d210 (change pattern 6 4)) = d328 pattern
  rw [s1209, s1270]
  rfl
theorem s1272 (pattern : Ten) : d330 (change pattern 6 4) = d328 pattern := by
  change d328 (change pattern 6 4) = d328 pattern
  exact s1271 pattern
theorem s1273 (pattern : Ten) : d331 (change pattern 6 4) = d571 pattern := by
  change (if pattern.d then d330 (change pattern 6 4) else d329 (change pattern 6 4)) = d571 pattern
  rw [s1272, s1269]
  rfl
theorem s1274 (pattern : Ten) : d0 (change pattern 6 10) = d0 pattern := by
  rfl
theorem s1275 (pattern : Ten) : d2 (change pattern 6 10) = d2 pattern := by
  rfl
theorem s1276 (pattern : Ten) : d15 (change pattern 6 10) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 6 10) else d0 (change pattern 6 10)) = d15 pattern
  rw [s1275, s1274]
  rfl
theorem s1277 (pattern : Ten) : d4 (change pattern 6 10) = d4 pattern := by
  rfl
theorem s1278 (pattern : Ten) : d10 (change pattern 6 10) = d10 pattern := by
  rfl
theorem s1279 (pattern : Ten) : d42 (change pattern 6 10) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d4 (change pattern 6 10)) = d42 pattern
  rw [s1278, s1277]
  rfl
theorem s1280 (pattern : Ten) : d48 (change pattern 6 10) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 6 10) else d15 (change pattern 6 10)) = d48 pattern
  rw [s1279, s1276]
  rfl
theorem s1281 (pattern : Ten) : d6 (change pattern 6 10) = d6 pattern := by
  rfl
theorem s1282 (pattern : Ten) : d43 (change pattern 6 10) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d6 (change pattern 6 10)) = d43 pattern
  rw [s1278, s1281]
  rfl
theorem s1283 (pattern : Ten) : d49 (change pattern 6 10) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d43 (change pattern 6 10)) = d49 pattern
  rw [s1278, s1282]
  rfl
theorem s1284 (pattern : Ten) : d54 (change pattern 6 10) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 6 10) else d48 (change pattern 6 10)) = d54 pattern
  rw [s1283, s1280]
  rfl
theorem s1285 (pattern : Ten) : d150 (change pattern 6 10) = d54 pattern := by
  change d54 (change pattern 6 10) = d54 pattern
  exact s1284 pattern
theorem s1286 (pattern : Ten) : d151 (change pattern 6 10) = d54 pattern := by
  change (if pattern.c then d54 (change pattern 6 10) else d150 (change pattern 6 10)) = d54 pattern
  rw [s1284, s1285]
  simp only [ite_self]
theorem s1287 (pattern : Ten) : d44 (change pattern 6 10) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 6 10) else d2 (change pattern 6 10)) = d44 pattern
  rw [s1277, s1275]
  rfl
theorem s1288 (pattern : Ten) : d50 (change pattern 6 10) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 6 10) else d44 (change pattern 6 10)) = d50 pattern
  rw [s1282, s1287]
  rfl
theorem s1289 (pattern : Ten) : d8 (change pattern 6 10) = d8 pattern := by
  rfl
theorem s1290 (pattern : Ten) : d45 (change pattern 6 10) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d8 (change pattern 6 10)) = d45 pattern
  rw [s1278, s1289]
  rfl
theorem s1291 (pattern : Ten) : d51 (change pattern 6 10) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d45 (change pattern 6 10)) = d51 pattern
  rw [s1278, s1290]
  rfl
theorem s1292 (pattern : Ten) : d55 (change pattern 6 10) = d55 pattern := by
  change (if pattern.h then d51 (change pattern 6 10) else d50 (change pattern 6 10)) = d55 pattern
  rw [s1291, s1288]
  rfl
theorem s1293 (pattern : Ten) : d152 (change pattern 6 10) = d152 pattern := by
  change (if pattern.c then d55 (change pattern 6 10) else d54 (change pattern 6 10)) = d152 pattern
  rw [s1292, s1284]
  rfl
theorem s1294 (pattern : Ten) : d154 (change pattern 6 10) = d572 pattern := by
  change (if pattern.e then d152 (change pattern 6 10) else d151 (change pattern 6 10)) = d572 pattern
  rw [s1293, s1286]
  rfl
theorem s1295 (pattern : Ten) : d7 (change pattern 6 10) = d7 pattern := by
  rfl
theorem s1296 (pattern : Ten) : d38 (change pattern 6 10) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 6 10) else d7 (change pattern 6 10)) = d38 pattern
  rw [s1289, s1295]
  rfl
theorem s1297 (pattern : Ten) : d40 (change pattern 6 10) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 6 10) else d38 (change pattern 6 10)) = d40 pattern
  rw [s1289, s1296]
  rfl
theorem s1298 (pattern : Ten) : d46 (change pattern 6 10) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d40 (change pattern 6 10)) = d46 pattern
  rw [s1278, s1297]
  rfl
theorem s1299 (pattern : Ten) : d52 (change pattern 6 10) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d46 (change pattern 6 10)) = d52 pattern
  rw [s1278, s1298]
  rfl
theorem s1300 (pattern : Ten) : d56 (change pattern 6 10) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 6 10) else d52 (change pattern 6 10)) = d56 pattern
  rw [s1278, s1299]
  rfl
theorem s1301 (pattern : Ten) : d9 (change pattern 6 10) = d9 pattern := by
  rfl
theorem s1302 (pattern : Ten) : d39 (change pattern 6 10) = d39 pattern := by
  change (if pattern.b then d10 (change pattern 6 10) else d9 (change pattern 6 10)) = d39 pattern
  rw [s1278, s1301]
  rfl
theorem s1303 (pattern : Ten) : d41 (change pattern 6 10) = d41 pattern := by
  change (if pattern.a then d10 (change pattern 6 10) else d39 (change pattern 6 10)) = d41 pattern
  rw [s1278, s1302]
  rfl
theorem s1304 (pattern : Ten) : d47 (change pattern 6 10) = d47 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d41 (change pattern 6 10)) = d47 pattern
  rw [s1278, s1303]
  rfl
theorem s1305 (pattern : Ten) : d53 (change pattern 6 10) = d53 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d47 (change pattern 6 10)) = d53 pattern
  rw [s1278, s1304]
  rfl
theorem s1306 (pattern : Ten) : d57 (change pattern 6 10) = d57 pattern := by
  change (if pattern.h then d10 (change pattern 6 10) else d53 (change pattern 6 10)) = d57 pattern
  rw [s1278, s1305]
  rfl
theorem s1307 (pattern : Ten) : d153 (change pattern 6 10) = d153 pattern := by
  change (if pattern.c then d57 (change pattern 6 10) else d56 (change pattern 6 10)) = d153 pattern
  rw [s1306, s1300]
  rfl
theorem s1308 (pattern : Ten) : d155 (change pattern 6 10) = d155 pattern := by
  change (if pattern.e then d153 (change pattern 6 10) else d56 (change pattern 6 10)) = d155 pattern
  rw [s1307, s1300]
  rfl
theorem s1309 (pattern : Ten) : d156 (change pattern 6 10) = d573 pattern := by
  change (if pattern.d then d155 (change pattern 6 10) else d154 (change pattern 6 10)) = d573 pattern
  rw [s1308, s1294]
  rfl
theorem s1310 (pattern : Ten) : d1 (change pattern 6 10) = d1 pattern := by
  rfl
theorem s1311 (pattern : Ten) : d171 (change pattern 6 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 6 10) else d0 (change pattern 6 10)) = d171 pattern
  rw [s1310, s1274]
  rfl
theorem s1312 (pattern : Ten) : d3 (change pattern 6 10) = d3 pattern := by
  rfl
theorem s1313 (pattern : Ten) : d172 (change pattern 6 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 6 10) else d2 (change pattern 6 10)) = d172 pattern
  rw [s1312, s1275]
  rfl
theorem s1314 (pattern : Ten) : d174 (change pattern 6 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 6 10) else d171 (change pattern 6 10)) = d174 pattern
  rw [s1313, s1311]
  rfl
theorem s1315 (pattern : Ten) : d5 (change pattern 6 10) = d5 pattern := by
  rfl
theorem s1316 (pattern : Ten) : d193 (change pattern 6 10) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 6 10) else d4 (change pattern 6 10)) = d193 pattern
  rw [s1315, s1277]
  rfl
theorem s1317 (pattern : Ten) : d197 (change pattern 6 10) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d193 (change pattern 6 10)) = d197 pattern
  rw [s1278, s1316]
  rfl
theorem s1318 (pattern : Ten) : d202 (change pattern 6 10) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 6 10) else d174 (change pattern 6 10)) = d202 pattern
  rw [s1317, s1314]
  rfl
theorem s1319 (pattern : Ten) : d194 (change pattern 6 10) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 6 10) else d6 (change pattern 6 10)) = d194 pattern
  rw [s1295, s1281]
  rfl
theorem s1320 (pattern : Ten) : d198 (change pattern 6 10) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d194 (change pattern 6 10)) = d198 pattern
  rw [s1278, s1319]
  rfl
theorem s1321 (pattern : Ten) : d203 (change pattern 6 10) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d198 (change pattern 6 10)) = d203 pattern
  rw [s1278, s1320]
  rfl
theorem s1322 (pattern : Ten) : d207 (change pattern 6 10) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 6 10) else d202 (change pattern 6 10)) = d207 pattern
  rw [s1321, s1318]
  rfl
theorem s1323 (pattern : Ten) : d211 (change pattern 6 10) = d207 pattern := by
  change d207 (change pattern 6 10) = d207 pattern
  exact s1322 pattern
theorem s1324 (pattern : Ten) : d326 (change pattern 6 10) = d207 pattern := by
  change (if pattern.c then d207 (change pattern 6 10) else d211 (change pattern 6 10)) = d207 pattern
  rw [s1322, s1323]
  simp only [ite_self]
theorem s1325 (pattern : Ten) : d309 (change pattern 6 10) = d309 pattern := by
  change (if pattern.a then d2 (change pattern 6 10) else d1 (change pattern 6 10)) = d309 pattern
  rw [s1275, s1310]
  rfl
theorem s1326 (pattern : Ten) : d313 (change pattern 6 10) = d313 pattern := by
  change (if pattern.f then d309 (change pattern 6 10) else d171 (change pattern 6 10)) = d313 pattern
  rw [s1325, s1311]
  rfl
theorem s1327 (pattern : Ten) : d310 (change pattern 6 10) = d310 pattern := by
  change (if pattern.a then d4 (change pattern 6 10) else d3 (change pattern 6 10)) = d310 pattern
  rw [s1277, s1312]
  rfl
theorem s1328 (pattern : Ten) : d314 (change pattern 6 10) = d314 pattern := by
  change (if pattern.f then d310 (change pattern 6 10) else d172 (change pattern 6 10)) = d314 pattern
  rw [s1327, s1313]
  rfl
theorem s1329 (pattern : Ten) : d317 (change pattern 6 10) = d317 pattern := by
  change (if pattern.j then d314 (change pattern 6 10) else d313 (change pattern 6 10)) = d317 pattern
  rw [s1328, s1326]
  rfl
theorem s1330 (pattern : Ten) : d311 (change pattern 6 10) = d311 pattern := by
  change (if pattern.a then d6 (change pattern 6 10) else d5 (change pattern 6 10)) = d311 pattern
  rw [s1281, s1315]
  rfl
theorem s1331 (pattern : Ten) : d315 (change pattern 6 10) = d315 pattern := by
  change (if pattern.f then d311 (change pattern 6 10) else d193 (change pattern 6 10)) = d315 pattern
  rw [s1330, s1316]
  rfl
theorem s1332 (pattern : Ten) : d318 (change pattern 6 10) = d318 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d315 (change pattern 6 10)) = d318 pattern
  rw [s1278, s1331]
  rfl
theorem s1333 (pattern : Ten) : d321 (change pattern 6 10) = d321 pattern := by
  change (if pattern.i then d318 (change pattern 6 10) else d317 (change pattern 6 10)) = d321 pattern
  rw [s1332, s1329]
  rfl
theorem s1334 (pattern : Ten) : d312 (change pattern 6 10) = d312 pattern := by
  change (if pattern.a then d8 (change pattern 6 10) else d7 (change pattern 6 10)) = d312 pattern
  rw [s1289, s1295]
  rfl
theorem s1335 (pattern : Ten) : d316 (change pattern 6 10) = d316 pattern := by
  change (if pattern.f then d312 (change pattern 6 10) else d194 (change pattern 6 10)) = d316 pattern
  rw [s1334, s1319]
  rfl
theorem s1336 (pattern : Ten) : d319 (change pattern 6 10) = d319 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d316 (change pattern 6 10)) = d319 pattern
  rw [s1278, s1335]
  rfl
theorem s1337 (pattern : Ten) : d322 (change pattern 6 10) = d322 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d319 (change pattern 6 10)) = d322 pattern
  rw [s1278, s1336]
  rfl
theorem s1338 (pattern : Ten) : d324 (change pattern 6 10) = d324 pattern := by
  change (if pattern.h then d322 (change pattern 6 10) else d321 (change pattern 6 10)) = d324 pattern
  rw [s1337, s1333]
  rfl
theorem s1339 (pattern : Ten) : d320 (change pattern 6 10) = d320 pattern := by
  change (if pattern.j then d315 (change pattern 6 10) else d314 (change pattern 6 10)) = d320 pattern
  rw [s1331, s1328]
  rfl
theorem s1340 (pattern : Ten) : d323 (change pattern 6 10) = d323 pattern := by
  change (if pattern.i then d319 (change pattern 6 10) else d320 (change pattern 6 10)) = d323 pattern
  rw [s1336, s1339]
  rfl
theorem s1341 (pattern : Ten) : d195 (change pattern 6 10) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 6 10) else d8 (change pattern 6 10)) = d195 pattern
  rw [s1301, s1289]
  rfl
theorem s1342 (pattern : Ten) : d11 (change pattern 6 10) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 6 10) else d9 (change pattern 6 10)) = d11 pattern
  rw [s1278, s1301]
  rfl
theorem s1343 (pattern : Ten) : d196 (change pattern 6 10) = d196 pattern := by
  change (if pattern.f then d11 (change pattern 6 10) else d195 (change pattern 6 10)) = d196 pattern
  rw [s1342, s1341]
  rfl
theorem s1344 (pattern : Ten) : d201 (change pattern 6 10) = d201 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d196 (change pattern 6 10)) = d201 pattern
  rw [s1278, s1343]
  rfl
theorem s1345 (pattern : Ten) : d206 (change pattern 6 10) = d206 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d201 (change pattern 6 10)) = d206 pattern
  rw [s1278, s1344]
  rfl
theorem s1346 (pattern : Ten) : d325 (change pattern 6 10) = d325 pattern := by
  change (if pattern.h then d206 (change pattern 6 10) else d323 (change pattern 6 10)) = d325 pattern
  rw [s1345, s1340]
  rfl
theorem s1347 (pattern : Ten) : d327 (change pattern 6 10) = d327 pattern := by
  change (if pattern.c then d325 (change pattern 6 10) else d324 (change pattern 6 10)) = d327 pattern
  rw [s1346, s1338]
  rfl
theorem s1348 (pattern : Ten) : d329 (change pattern 6 10) = d574 pattern := by
  change (if pattern.e then d327 (change pattern 6 10) else d326 (change pattern 6 10)) = d574 pattern
  rw [s1347, s1324]
  rfl
theorem s1349 (pattern : Ten) : d200 (change pattern 6 10) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 6 10) else d195 (change pattern 6 10)) = d200 pattern
  rw [s1278, s1341]
  rfl
end NetHack.Sokoban41.Diagram
