/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions66
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8040 (p : Pattern) : d1225 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1181 (change p 163 (some 141)) else d1177 (change p 163 (some 141))) = d4311 p
  rw [sub8012, sub8039]
  rfl
theorem sub8041 (p : Pattern) : d1226 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1225 (change p 163 (some 141))) = d4313 p
  rw [sub8014, sub8040]
  rfl
theorem sub8042 (p : Pattern) : d1227 (change p 163 (some 141)) = d4321 p := by
  change (if p 160 then d1189 (change p 163 (some 141)) else d1226 (change p 163 (some 141))) = d4321 p
  rw [sub8017, sub8041]
  rfl
theorem sub8043 (p : Pattern) : d1228 (change p 163 (some 141)) = d4321 p := by
  change d1227 (change p 163 (some 141)) = d4321 p
  exact sub8042 p
theorem sub8044 (p : Pattern) : d1229 (change p 163 (some 141)) = d5244 p := by
  change (if p 138 then d1228 (change p 163 (some 141)) else d1221 (change p 163 (some 141))) = d5244 p
  rw [sub8043, sub8038]
  rfl
theorem sub8045 (p : Pattern) : d1233 (change p 163 (some 141)) = d4321 p := by
  change d1227 (change p 163 (some 141)) = d4321 p
  exact sub8042 p
theorem sub8046 (p : Pattern) : d1234 (change p 163 (some 141)) = d5247 p := by
  change (if p 138 then d12 (change p 163 (some 141)) else d1233 (change p 163 (some 141))) = d5247 p
  rw [sub7979, sub8045]
  rfl
theorem sub8047 (p : Pattern) : d1235 (change p 163 (some 141)) = d5248 p := by
  change (if p 116 then d1234 (change p 163 (some 141)) else d1229 (change p 163 (some 141))) = d5248 p
  rw [sub8046, sub8044]
  rfl
theorem sub8048 (p : Pattern) : d1236 (change p 163 (some 141)) = d5249 p := by
  change (if p 115 then d1235 (change p 163 (some 141)) else d1207 (change p 163 (some 141))) = d5249 p
  rw [sub8047, sub8031]
  rfl
theorem sub8049 (p : Pattern) : d1208 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub8050 (p : Pattern) : d1245 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1167 (change p 163 (some 141)) else d1208 (change p 163 (some 141))) = d4311 p
  rw [sub7992, sub8049]
  rfl
theorem sub8051 (p : Pattern) : d1246 (change p 163 (some 141)) = d4312 p := by
  change (if p 162 then d63 (change p 163 (some 141)) else d1170 (change p 163 (some 141))) = d4312 p
  rw [sub7998, sub8001]
  rfl
theorem sub8052 (p : Pattern) : d1247 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1246 (change p 163 (some 141)) else d1245 (change p 163 (some 141))) = d4313 p
  rw [sub8051, sub8050]
  rfl
theorem sub8053 (p : Pattern) : d1248 (change p 163 (some 141)) = d4317 p := by
  change (if p 160 then d1219 (change p 163 (some 141)) else d1247 (change p 163 (some 141))) = d4317 p
  rw [sub8036, sub8052]
  rfl
theorem sub8054 (p : Pattern) : d1249 (change p 163 (some 141)) = d4317 p := by
  change d1248 (change p 163 (some 141)) = d4317 p
  exact sub8053 p
theorem sub8055 (p : Pattern) : d1193 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub8056 (p : Pattern) : d1253 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1181 (change p 163 (some 141)) else d1193 (change p 163 (some 141))) = d4311 p
  rw [sub8012, sub8055]
  rfl
theorem sub8057 (p : Pattern) : d1254 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1253 (change p 163 (some 141))) = d4313 p
  rw [sub8014, sub8056]
  rfl
theorem sub8058 (p : Pattern) : d1255 (change p 163 (some 141)) = d4321 p := by
  change (if p 160 then d1189 (change p 163 (some 141)) else d1254 (change p 163 (some 141))) = d4321 p
  rw [sub8017, sub8057]
  rfl
theorem sub8059 (p : Pattern) : d1256 (change p 163 (some 141)) = d4321 p := by
  change d1255 (change p 163 (some 141)) = d4321 p
  exact sub8058 p
theorem sub8060 (p : Pattern) : d1257 (change p 163 (some 141)) = d5244 p := by
  change (if p 138 then d1256 (change p 163 (some 141)) else d1249 (change p 163 (some 141))) = d5244 p
  rw [sub8059, sub8054]
  rfl
theorem sub8061 (p : Pattern) : d1258 (change p 163 (some 141)) = d5245 p := by
  change (if p 138 then d1205 (change p 163 (some 141)) else d1191 (change p 163 (some 141))) = d5245 p
  rw [sub8029, sub8019]
  rfl
theorem sub8062 (p : Pattern) : d1259 (change p 163 (some 141)) = d5246 p := by
  change (if p 116 then d1258 (change p 163 (some 141)) else d1257 (change p 163 (some 141))) = d5246 p
  rw [sub8061, sub8060]
  rfl
theorem sub8063 (p : Pattern) : d1261 (change p 163 (some 141)) = d4317 p := by
  change (if p 160 then d1219 (change p 163 (some 141)) else d1199 (change p 163 (some 141))) = d4317 p
  rw [sub8036, sub8023]
  rfl
theorem sub8064 (p : Pattern) : d1262 (change p 163 (some 141)) = d4317 p := by
  change d1261 (change p 163 (some 141)) = d4317 p
  exact sub8063 p
theorem sub8065 (p : Pattern) : d1265 (change p 163 (some 141)) = d4321 p := by
  change d1227 (change p 163 (some 141)) = d4321 p
  exact sub8042 p
theorem sub8066 (p : Pattern) : d1266 (change p 163 (some 141)) = d5244 p := by
  change (if p 138 then d1265 (change p 163 (some 141)) else d1262 (change p 163 (some 141))) = d5244 p
  rw [sub8065, sub8064]
  rfl
theorem sub8067 (p : Pattern) : d1267 (change p 163 (some 141)) = d5247 p := by
  change (if p 138 then d12 (change p 163 (some 141)) else d1228 (change p 163 (some 141))) = d5247 p
  rw [sub7979, sub8043]
  rfl
theorem sub8068 (p : Pattern) : d1268 (change p 163 (some 141)) = d5248 p := by
  change (if p 116 then d1267 (change p 163 (some 141)) else d1266 (change p 163 (some 141))) = d5248 p
  rw [sub8067, sub8066]
  rfl
theorem sub8069 (p : Pattern) : d1269 (change p 163 (some 141)) = d5249 p := by
  change (if p 115 then d1268 (change p 163 (some 141)) else d1259 (change p 163 (some 141))) = d5249 p
  rw [sub8068, sub8062]
  rfl
theorem sub8070 (p : Pattern) : d1270 (change p 163 (some 141)) = d5249 p := by
  change (if p 71 then d1269 (change p 163 (some 141)) else d1236 (change p 163 (some 141))) = d5249 p
  rw [sub8069, sub8048]
  simp only [ite_self]
theorem sub8071 (p : Pattern) : d1 (change p 163 (some 141)) = d1 p := by
  rfl
theorem sub8072 (p : Pattern) : d102 (change p 163 (some 141)) = d102 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d1 (change p 163 (some 141))) = d102 p
  rw [sub7979, sub8071]
  rfl
theorem sub8073 (p : Pattern) : d103 (change p 163 (some 141)) = d103 p := by
  change (if p 246 then d102 (change p 163 (some 141)) else d1 (change p 163 (some 141))) = d103 p
  rw [sub8072, sub8071]
  rfl
theorem sub8074 (p : Pattern) : d104 (change p 163 (some 141)) = d104 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d103 (change p 163 (some 141))) = d104 p
  rw [sub7979, sub8073]
  rfl
theorem sub8075 (p : Pattern) : d105 (change p 163 (some 141)) = d105 p := by
  change (if p 182 then d104 (change p 163 (some 141)) else d103 (change p 163 (some 141))) = d105 p
  rw [sub8074, sub8073]
  rfl
theorem sub8076 (p : Pattern) : d1283 (change p 163 (some 141)) = d105 p := by
  change d105 (change p 163 (some 141)) = d105 p
  exact sub8075 p
theorem sub8077 (p : Pattern) : d3 (change p 163 (some 141)) = d3 p := by
  rfl
theorem sub8078 (p : Pattern) : d115 (change p 163 (some 141)) = d115 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d3 (change p 163 (some 141))) = d115 p
  rw [sub7979, sub8077]
  rfl
theorem sub8079 (p : Pattern) : d116 (change p 163 (some 141)) = d116 p := by
  change (if p 246 then d115 (change p 163 (some 141)) else d3 (change p 163 (some 141))) = d116 p
  rw [sub8078, sub8077]
  rfl
theorem sub8080 (p : Pattern) : d117 (change p 163 (some 141)) = d117 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d116 (change p 163 (some 141))) = d117 p
  rw [sub7979, sub8079]
  rfl
theorem sub8081 (p : Pattern) : d132 (change p 163 (some 141)) = d132 p := by
  change (if p 182 then d117 (change p 163 (some 141)) else d116 (change p 163 (some 141))) = d132 p
  rw [sub8080, sub8079]
  rfl
theorem sub8082 (p : Pattern) : d1284 (change p 163 (some 141)) = d132 p := by
  change d132 (change p 163 (some 141)) = d132 p
  exact sub8081 p
theorem sub8083 (p : Pattern) : d1285 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1284 (change p 163 (some 141)) else d1283 (change p 163 (some 141))) = d4339 p
  rw [sub8082, sub8076]
  rfl
theorem sub8084 (p : Pattern) : d1286 (change p 163 (some 141)) = d132 p := by
  change d132 (change p 163 (some 141)) = d132 p
  exact sub8081 p
theorem sub8085 (p : Pattern) : d1287 (change p 163 (some 141)) = d1061 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1286 (change p 163 (some 141))) = d1061 p
  rw [sub7979, sub8084]
  rfl
theorem sub8086 (p : Pattern) : d1288 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1287 (change p 163 (some 141)) else d1285 (change p 163 (some 141))) = d4340 p
  rw [sub8085, sub8083]
  rfl
theorem sub8087 (p : Pattern) : d1289 (change p 163 (some 141)) = d132 p := by
  change d132 (change p 163 (some 141)) = d132 p
  exact sub8081 p
theorem sub8088 (p : Pattern) : d139 (change p 163 (some 141)) = d139 p := by
  change (if p 182 then d12 (change p 163 (some 141)) else d116 (change p 163 (some 141))) = d139 p
  rw [sub7979, sub8079]
  rfl
theorem sub8089 (p : Pattern) : d1290 (change p 163 (some 141)) = d139 p := by
  change d139 (change p 163 (some 141)) = d139 p
  exact sub8088 p
theorem sub8090 (p : Pattern) : d1291 (change p 163 (some 141)) = d4341 p := by
  change (if p 162 then d1290 (change p 163 (some 141)) else d1289 (change p 163 (some 141))) = d4341 p
  rw [sub8089, sub8087]
  rfl
theorem sub8091 (p : Pattern) : d1292 (change p 163 (some 141)) = d4342 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1290 (change p 163 (some 141))) = d4342 p
  rw [sub7979, sub8089]
  rfl
theorem sub8092 (p : Pattern) : d1293 (change p 163 (some 141)) = d4343 p := by
  change (if p 161 then d1292 (change p 163 (some 141)) else d1291 (change p 163 (some 141))) = d4343 p
  rw [sub8091, sub8090]
  rfl
theorem sub8093 (p : Pattern) : d1294 (change p 163 (some 141)) = d4344 p := by
  change (if p 160 then d1293 (change p 163 (some 141)) else d1288 (change p 163 (some 141))) = d4344 p
  rw [sub8092, sub8086]
  rfl
theorem sub8094 (p : Pattern) : d1295 (change p 163 (some 141)) = d4344 p := by
  change d1294 (change p 163 (some 141)) = d4344 p
  exact sub8093 p
theorem sub8095 (p : Pattern) : d1303 (change p 163 (some 141)) = d105 p := by
  change d105 (change p 163 (some 141)) = d105 p
  exact sub8075 p
theorem sub8096 (p : Pattern) : d1304 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1289 (change p 163 (some 141)) else d1303 (change p 163 (some 141))) = d4339 p
  rw [sub8087, sub8095]
  rfl
theorem sub8097 (p : Pattern) : d1300 (change p 163 (some 141)) = d1061 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1289 (change p 163 (some 141))) = d1061 p
  rw [sub7979, sub8087]
  rfl
theorem sub8098 (p : Pattern) : d1305 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1300 (change p 163 (some 141)) else d1304 (change p 163 (some 141))) = d4340 p
  rw [sub8097, sub8096]
  rfl
theorem sub8099 (p : Pattern) : d1301 (change p 163 (some 141)) = d1062 p := by
  change (if p 161 then d12 (change p 163 (some 141)) else d1300 (change p 163 (some 141))) = d1062 p
  rw [sub7979, sub8097]
  rfl
theorem sub8100 (p : Pattern) : d1306 (change p 163 (some 141)) = d4347 p := by
  change (if p 160 then d1301 (change p 163 (some 141)) else d1305 (change p 163 (some 141))) = d4347 p
  rw [sub8099, sub8098]
  rfl
theorem sub8101 (p : Pattern) : d1307 (change p 163 (some 141)) = d4347 p := by
  change d1306 (change p 163 (some 141)) = d4347 p
  exact sub8100 p
theorem sub8102 (p : Pattern) : d1308 (change p 163 (some 141)) = d5250 p := by
  change (if p 138 then d1307 (change p 163 (some 141)) else d1295 (change p 163 (some 141))) = d5250 p
  rw [sub8101, sub8094]
  rfl
theorem sub8103 (p : Pattern) : d1312 (change p 163 (some 141)) = d105 p := by
  change d105 (change p 163 (some 141)) = d105 p
  exact sub8075 p
theorem sub8104 (p : Pattern) : d1313 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1289 (change p 163 (some 141)) else d1312 (change p 163 (some 141))) = d4339 p
  rw [sub8087, sub8103]
  rfl
theorem sub8105 (p : Pattern) : d1314 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1300 (change p 163 (some 141)) else d1313 (change p 163 (some 141))) = d4340 p
  rw [sub8097, sub8104]
  rfl
theorem sub8106 (p : Pattern) : d1315 (change p 163 (some 141)) = d4347 p := by
  change (if p 160 then d1301 (change p 163 (some 141)) else d1314 (change p 163 (some 141))) = d4347 p
  rw [sub8099, sub8105]
  rfl
theorem sub8107 (p : Pattern) : d1316 (change p 163 (some 141)) = d4347 p := by
  change d1315 (change p 163 (some 141)) = d4347 p
  exact sub8106 p
theorem sub8108 (p : Pattern) : d162 (change p 163 (some 141)) = d12 p := by
  change d12 (change p 163 (some 141)) = d12 p
  exact sub7979 p
theorem sub8109 (p : Pattern) : d1317 (change p 163 (some 141)) = d5251 p := by
  change (if p 138 then d162 (change p 163 (some 141)) else d1316 (change p 163 (some 141))) = d5251 p
  rw [sub8108, sub8107]
  rfl
theorem sub8110 (p : Pattern) : d1318 (change p 163 (some 141)) = d5252 p := by
  change (if p 116 then d1317 (change p 163 (some 141)) else d1308 (change p 163 (some 141))) = d5252 p
  rw [sub8109, sub8102]
  rfl
theorem sub8111 (p : Pattern) : d1274 (change p 163 (some 141)) = d105 p := by
  change d105 (change p 163 (some 141)) = d105 p
  exact sub8075 p
theorem sub8112 (p : Pattern) : d1326 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1289 (change p 163 (some 141)) else d1274 (change p 163 (some 141))) = d4339 p
  rw [sub8087, sub8111]
  rfl
theorem sub8113 (p : Pattern) : d1327 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1300 (change p 163 (some 141)) else d1326 (change p 163 (some 141))) = d4340 p
  rw [sub8097, sub8112]
  rfl
theorem sub8114 (p : Pattern) : d1328 (change p 163 (some 141)) = d4344 p := by
  change (if p 160 then d1293 (change p 163 (some 141)) else d1327 (change p 163 (some 141))) = d4344 p
  rw [sub8092, sub8113]
  rfl
theorem sub8115 (p : Pattern) : d1329 (change p 163 (some 141)) = d4344 p := by
  change d1328 (change p 163 (some 141)) = d4344 p
  exact sub8114 p
theorem sub8116 (p : Pattern) : d1296 (change p 163 (some 141)) = d105 p := by
  change d105 (change p 163 (some 141)) = d105 p
  exact sub8075 p
theorem sub8117 (p : Pattern) : d1332 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1289 (change p 163 (some 141)) else d1296 (change p 163 (some 141))) = d4339 p
  rw [sub8087, sub8116]
  rfl
theorem sub8118 (p : Pattern) : d1333 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1300 (change p 163 (some 141)) else d1332 (change p 163 (some 141))) = d4340 p
  rw [sub8097, sub8117]
  rfl
theorem sub8119 (p : Pattern) : d1334 (change p 163 (some 141)) = d4347 p := by
  change (if p 160 then d1301 (change p 163 (some 141)) else d1333 (change p 163 (some 141))) = d4347 p
  rw [sub8099, sub8118]
  rfl
theorem sub8120 (p : Pattern) : d1335 (change p 163 (some 141)) = d4347 p := by
  change d1334 (change p 163 (some 141)) = d4347 p
  exact sub8119 p
theorem sub8121 (p : Pattern) : d1336 (change p 163 (some 141)) = d5250 p := by
  change (if p 138 then d1335 (change p 163 (some 141)) else d1329 (change p 163 (some 141))) = d5250 p
  rw [sub8120, sub8115]
  rfl
theorem sub8122 (p : Pattern) : d1340 (change p 163 (some 141)) = d4347 p := by
  change d1334 (change p 163 (some 141)) = d4347 p
  exact sub8119 p
theorem sub8123 (p : Pattern) : d1341 (change p 163 (some 141)) = d5251 p := by
  change (if p 138 then d12 (change p 163 (some 141)) else d1340 (change p 163 (some 141))) = d5251 p
  rw [sub7979, sub8122]
  rfl
theorem sub8124 (p : Pattern) : d1342 (change p 163 (some 141)) = d5252 p := by
  change (if p 116 then d1341 (change p 163 (some 141)) else d1336 (change p 163 (some 141))) = d5252 p
  rw [sub8123, sub8121]
  rfl
theorem sub8125 (p : Pattern) : d1343 (change p 163 (some 141)) = d5252 p := by
  change (if p 115 then d1342 (change p 163 (some 141)) else d1318 (change p 163 (some 141))) = d5252 p
  rw [sub8124, sub8110]
  simp only [ite_self]
theorem sub8126 (p : Pattern) : d1344 (change p 163 (some 141)) = d5253 p := by
  change (if p 71 then d1343 (change p 163 (some 141)) else d1236 (change p 163 (some 141))) = d5253 p
  rw [sub8125, sub8048]
  rfl
theorem sub8127 (p : Pattern) : d1345 (change p 163 (some 141)) = d5254 p := by
  change (if p 49 then d1344 (change p 163 (some 141)) else d1270 (change p 163 (some 141))) = d5254 p
  rw [sub8126, sub8070]
  rfl
theorem sub8128 (p : Pattern) : d1346 (change p 163 (some 141)) = d4361 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1181 (change p 163 (some 141))) = d4361 p
  rw [sub8014, sub8012]
  rfl
theorem sub8129 (p : Pattern) : d4 (change p 163 (some 141)) = d4 p := by
  rfl
theorem sub8130 (p : Pattern) : d17 (change p 163 (some 141)) = d17 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d4 (change p 163 (some 141))) = d17 p
  rw [sub7979, sub8129]
  rfl
theorem sub8131 (p : Pattern) : d18 (change p 163 (some 141)) = d18 p := by
  change (if p 246 then d17 (change p 163 (some 141)) else d4 (change p 163 (some 141))) = d18 p
  rw [sub8130, sub8129]
  rfl
theorem sub8132 (p : Pattern) : d19 (change p 163 (some 141)) = d19 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d18 (change p 163 (some 141))) = d19 p
  rw [sub7979, sub8131]
  rfl
theorem sub8133 (p : Pattern) : d20 (change p 163 (some 141)) = d20 p := by
  change (if p 182 then d19 (change p 163 (some 141)) else d18 (change p 163 (some 141))) = d20 p
  rw [sub8132, sub8131]
  rfl
theorem sub8134 (p : Pattern) : d1347 (change p 163 (some 141)) = d20 p := by
  change d20 (change p 163 (some 141)) = d20 p
  exact sub8133 p
theorem sub8135 (p : Pattern) : d1348 (change p 163 (some 141)) = d1100 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1347 (change p 163 (some 141))) = d1100 p
  rw [sub7979, sub8134]
  rfl
theorem sub8136 (p : Pattern) : d1349 (change p 163 (some 141)) = d1101 p := by
  change (if p 161 then d12 (change p 163 (some 141)) else d1348 (change p 163 (some 141))) = d1101 p
  rw [sub7979, sub8135]
  rfl
theorem sub8137 (p : Pattern) : d1350 (change p 163 (some 141)) = d4362 p := by
  change (if p 160 then d1349 (change p 163 (some 141)) else d1346 (change p 163 (some 141))) = d4362 p
  rw [sub8136, sub8128]
  rfl
theorem sub8138 (p : Pattern) : d1351 (change p 163 (some 141)) = d4362 p := by
  change d1350 (change p 163 (some 141)) = d4362 p
  exact sub8137 p
theorem sub8139 (p : Pattern) : d1352 (change p 163 (some 141)) = d5255 p := by
  change (if p 138 then d1351 (change p 163 (some 141)) else d1262 (change p 163 (some 141))) = d5255 p
  rw [sub8138, sub8064]
  rfl
theorem sub8140 (p : Pattern) : d1353 (change p 163 (some 141)) = d4362 p := by
  change d1350 (change p 163 (some 141)) = d4362 p
  exact sub8137 p
theorem sub8141 (p : Pattern) : d1354 (change p 163 (some 141)) = d5256 p := by
  change (if p 138 then d12 (change p 163 (some 141)) else d1353 (change p 163 (some 141))) = d5256 p
  rw [sub7979, sub8140]
  rfl
theorem sub8142 (p : Pattern) : d1355 (change p 163 (some 141)) = d5257 p := by
  change (if p 116 then d1354 (change p 163 (some 141)) else d1352 (change p 163 (some 141))) = d5257 p
  rw [sub8141, sub8139]
  rfl
theorem sub8143 (p : Pattern) : d1356 (change p 163 (some 141)) = d5258 p := by
  change (if p 115 then d1355 (change p 163 (some 141)) else d1259 (change p 163 (some 141))) = d5258 p
  rw [sub8142, sub8062]
  rfl
theorem sub8144 (p : Pattern) : d1357 (change p 163 (some 141)) = d5259 p := by
  change (if p 71 then d1356 (change p 163 (some 141)) else d1236 (change p 163 (some 141))) = d5259 p
  rw [sub8143, sub8048]
  rfl
theorem sub8145 (p : Pattern) : d1358 (change p 163 (some 141)) = d4339 p := by
  change (if p 162 then d1289 (change p 163 (some 141)) else d1283 (change p 163 (some 141))) = d4339 p
  rw [sub8087, sub8076]
  rfl
theorem sub8146 (p : Pattern) : d1359 (change p 163 (some 141)) = d4340 p := by
  change (if p 161 then d1300 (change p 163 (some 141)) else d1358 (change p 163 (some 141))) = d4340 p
  rw [sub8097, sub8145]
  rfl
theorem sub8147 (p : Pattern) : d1360 (change p 163 (some 141)) = d4344 p := by
  change (if p 160 then d1293 (change p 163 (some 141)) else d1359 (change p 163 (some 141))) = d4344 p
  rw [sub8092, sub8146]
  rfl
theorem sub8148 (p : Pattern) : d1361 (change p 163 (some 141)) = d4344 p := by
  change d1360 (change p 163 (some 141)) = d4344 p
  exact sub8147 p
theorem sub8149 (p : Pattern) : d1362 (change p 163 (some 141)) = d4347 p := by
  change d1334 (change p 163 (some 141)) = d4347 p
  exact sub8119 p
theorem sub8150 (p : Pattern) : d1363 (change p 163 (some 141)) = d5250 p := by
  change (if p 138 then d1362 (change p 163 (some 141)) else d1361 (change p 163 (some 141))) = d5250 p
  rw [sub8149, sub8148]
  rfl
theorem sub8151 (p : Pattern) : d1364 (change p 163 (some 141)) = d4347 p := by
  change d1334 (change p 163 (some 141)) = d4347 p
  exact sub8119 p
theorem sub8152 (p : Pattern) : d1365 (change p 163 (some 141)) = d5251 p := by
  change (if p 138 then d162 (change p 163 (some 141)) else d1364 (change p 163 (some 141))) = d5251 p
  rw [sub8108, sub8151]
  rfl
theorem sub8153 (p : Pattern) : d1366 (change p 163 (some 141)) = d5252 p := by
  change (if p 116 then d1365 (change p 163 (some 141)) else d1363 (change p 163 (some 141))) = d5252 p
  rw [sub8152, sub8150]
  rfl
theorem sub8154 (p : Pattern) : d5 (change p 163 (some 141)) = d5 p := by
  rfl
theorem sub8155 (p : Pattern) : d106 (change p 163 (some 141)) = d106 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d5 (change p 163 (some 141))) = d106 p
  rw [sub7979, sub8154]
  rfl
theorem sub8156 (p : Pattern) : d107 (change p 163 (some 141)) = d107 p := by
  change (if p 246 then d106 (change p 163 (some 141)) else d5 (change p 163 (some 141))) = d107 p
  rw [sub8155, sub8154]
  rfl
theorem sub8157 (p : Pattern) : d282 (change p 163 (some 141)) = d282 p := by
  change (if p 204 then d107 (change p 163 (some 141)) else d116 (change p 163 (some 141))) = d282 p
  rw [sub8156, sub8079]
  rfl
theorem sub8158 (p : Pattern) : d283 (change p 163 (some 141)) = d283 p := by
  change (if p 182 then d12 (change p 163 (some 141)) else d282 (change p 163 (some 141))) = d283 p
  rw [sub7979, sub8157]
  rfl
theorem sub8159 (p : Pattern) : d1375 (change p 163 (some 141)) = d283 p := by
  change d283 (change p 163 (some 141)) = d283 p
  exact sub8158 p
end NetHack.Sokoban22Refined85
