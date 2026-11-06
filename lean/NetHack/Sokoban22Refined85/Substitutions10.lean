/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1200 (p : Pattern) : d169 (change p 48 none) = d169 p := by
  change (if p 49 then d168 (change p 48 none) else d101 (change p 48 none)) = d169 p
  rw [sub1199, sub1128]
  rfl
theorem sub1201 (p : Pattern) : d481 (change p 48 none) = d169 p := by
  change d169 (change p 48 none) = d169 p
  exact sub1200 p
theorem sub1202 (p : Pattern) : d0 (change p 49 (some 48)) = d0 p := by
  rfl
theorem sub1203 (p : Pattern) : d12 (change p 49 (some 48)) = d12 p := by
  rfl
theorem sub1204 (p : Pattern) : d13 (change p 49 (some 48)) = d13 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d0 (change p 49 (some 48))) = d13 p
  rw [sub1203, sub1202]
  rfl
theorem sub1205 (p : Pattern) : d14 (change p 49 (some 48)) = d14 p := by
  change (if p 246 then d13 (change p 49 (some 48)) else d0 (change p 49 (some 48))) = d14 p
  rw [sub1204, sub1202]
  rfl
theorem sub1206 (p : Pattern) : d15 (change p 49 (some 48)) = d15 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d15 p
  rw [sub1203, sub1205]
  rfl
theorem sub1207 (p : Pattern) : d16 (change p 49 (some 48)) = d16 p := by
  change (if p 182 then d15 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d16 p
  rw [sub1206, sub1205]
  rfl
theorem sub1208 (p : Pattern) : d4 (change p 49 (some 48)) = d4 p := by
  rfl
theorem sub1209 (p : Pattern) : d17 (change p 49 (some 48)) = d17 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d4 (change p 49 (some 48))) = d17 p
  rw [sub1203, sub1208]
  rfl
theorem sub1210 (p : Pattern) : d18 (change p 49 (some 48)) = d18 p := by
  change (if p 246 then d17 (change p 49 (some 48)) else d4 (change p 49 (some 48))) = d18 p
  rw [sub1209, sub1208]
  rfl
theorem sub1211 (p : Pattern) : d19 (change p 49 (some 48)) = d19 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d18 (change p 49 (some 48))) = d19 p
  rw [sub1203, sub1210]
  rfl
theorem sub1212 (p : Pattern) : d20 (change p 49 (some 48)) = d20 p := by
  change (if p 182 then d19 (change p 49 (some 48)) else d18 (change p 49 (some 48))) = d20 p
  rw [sub1211, sub1210]
  rfl
theorem sub1213 (p : Pattern) : d21 (change p 49 (some 48)) = d21 p := by
  change (if p 163 then d20 (change p 49 (some 48)) else d16 (change p 49 (some 48))) = d21 p
  rw [sub1212, sub1207]
  rfl
theorem sub1214 (p : Pattern) : d22 (change p 49 (some 48)) = d22 p := by
  change (if p 162 then d21 (change p 49 (some 48)) else d16 (change p 49 (some 48))) = d22 p
  rw [sub1213, sub1207]
  rfl
theorem sub1215 (p : Pattern) : d9 (change p 49 (some 48)) = d9 p := by
  rfl
theorem sub1216 (p : Pattern) : d23 (change p 49 (some 48)) = d23 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d9 (change p 49 (some 48))) = d23 p
  rw [sub1203, sub1215]
  rfl
theorem sub1217 (p : Pattern) : d24 (change p 49 (some 48)) = d24 p := by
  change (if p 246 then d23 (change p 49 (some 48)) else d9 (change p 49 (some 48))) = d24 p
  rw [sub1216, sub1215]
  rfl
theorem sub1218 (p : Pattern) : d25 (change p 49 (some 48)) = d25 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d24 (change p 49 (some 48))) = d25 p
  rw [sub1203, sub1217]
  rfl
theorem sub1219 (p : Pattern) : d26 (change p 49 (some 48)) = d26 p := by
  change (if p 182 then d25 (change p 49 (some 48)) else d24 (change p 49 (some 48))) = d26 p
  rw [sub1218, sub1217]
  rfl
theorem sub1220 (p : Pattern) : d27 (change p 49 (some 48)) = d27 p := by
  change (if p 163 then d12 (change p 49 (some 48)) else d26 (change p 49 (some 48))) = d27 p
  rw [sub1203, sub1219]
  rfl
theorem sub1221 (p : Pattern) : d28 (change p 49 (some 48)) = d28 p := by
  change (if p 162 then d27 (change p 49 (some 48)) else d21 (change p 49 (some 48))) = d28 p
  rw [sub1220, sub1213]
  rfl
theorem sub1222 (p : Pattern) : d29 (change p 49 (some 48)) = d29 p := by
  change (if p 161 then d28 (change p 49 (some 48)) else d22 (change p 49 (some 48))) = d29 p
  rw [sub1221, sub1214]
  rfl
theorem sub1223 (p : Pattern) : d2 (change p 49 (some 48)) = d2 p := by
  rfl
theorem sub1224 (p : Pattern) : d30 (change p 49 (some 48)) = d30 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d2 (change p 49 (some 48))) = d30 p
  rw [sub1203, sub1223]
  rfl
theorem sub1225 (p : Pattern) : d31 (change p 49 (some 48)) = d31 p := by
  change (if p 246 then d30 (change p 49 (some 48)) else d2 (change p 49 (some 48))) = d31 p
  rw [sub1224, sub1223]
  rfl
theorem sub1226 (p : Pattern) : d32 (change p 49 (some 48)) = d32 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d31 (change p 49 (some 48))) = d32 p
  rw [sub1203, sub1225]
  rfl
theorem sub1227 (p : Pattern) : d33 (change p 49 (some 48)) = d33 p := by
  change (if p 182 then d32 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d33 p
  rw [sub1226, sub1205]
  rfl
theorem sub1228 (p : Pattern) : d6 (change p 49 (some 48)) = d6 p := by
  rfl
theorem sub1229 (p : Pattern) : d34 (change p 49 (some 48)) = d34 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d6 (change p 49 (some 48))) = d34 p
  rw [sub1203, sub1228]
  rfl
theorem sub1230 (p : Pattern) : d35 (change p 49 (some 48)) = d35 p := by
  change (if p 246 then d34 (change p 49 (some 48)) else d6 (change p 49 (some 48))) = d35 p
  rw [sub1229, sub1228]
  rfl
theorem sub1231 (p : Pattern) : d36 (change p 49 (some 48)) = d36 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d35 (change p 49 (some 48))) = d36 p
  rw [sub1203, sub1230]
  rfl
theorem sub1232 (p : Pattern) : d37 (change p 49 (some 48)) = d37 p := by
  change (if p 182 then d36 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d37 p
  rw [sub1231, sub1205]
  rfl
theorem sub1233 (p : Pattern) : d38 (change p 49 (some 48)) = d38 p := by
  change (if p 163 then d37 (change p 49 (some 48)) else d33 (change p 49 (some 48))) = d38 p
  rw [sub1232, sub1227]
  rfl
theorem sub1234 (p : Pattern) : d11 (change p 49 (some 48)) = d11 p := by
  rfl
theorem sub1235 (p : Pattern) : d39 (change p 49 (some 48)) = d39 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d11 (change p 49 (some 48))) = d39 p
  rw [sub1203, sub1234]
  rfl
theorem sub1236 (p : Pattern) : d40 (change p 49 (some 48)) = d40 p := by
  change (if p 246 then d39 (change p 49 (some 48)) else d11 (change p 49 (some 48))) = d40 p
  rw [sub1235, sub1234]
  rfl
theorem sub1237 (p : Pattern) : d41 (change p 49 (some 48)) = d41 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d40 (change p 49 (some 48))) = d41 p
  rw [sub1203, sub1236]
  rfl
theorem sub1238 (p : Pattern) : d42 (change p 49 (some 48)) = d42 p := by
  change (if p 182 then d41 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d42 p
  rw [sub1237, sub1205]
  rfl
theorem sub1239 (p : Pattern) : d43 (change p 49 (some 48)) = d43 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d18 (change p 49 (some 48))) = d43 p
  rw [sub1203, sub1210]
  rfl
theorem sub1240 (p : Pattern) : d44 (change p 49 (some 48)) = d44 p := by
  change (if p 163 then d43 (change p 49 (some 48)) else d42 (change p 49 (some 48))) = d44 p
  rw [sub1239, sub1238]
  rfl
theorem sub1241 (p : Pattern) : d45 (change p 49 (some 48)) = d45 p := by
  change (if p 162 then d44 (change p 49 (some 48)) else d38 (change p 49 (some 48))) = d45 p
  rw [sub1240, sub1233]
  rfl
theorem sub1242 (p : Pattern) : d46 (change p 49 (some 48)) = d46 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d14 (change p 49 (some 48))) = d46 p
  rw [sub1203, sub1205]
  rfl
theorem sub1243 (p : Pattern) : d47 (change p 49 (some 48)) = d47 p := by
  change (if p 163 then d43 (change p 49 (some 48)) else d46 (change p 49 (some 48))) = d47 p
  rw [sub1239, sub1242]
  rfl
theorem sub1244 (p : Pattern) : d48 (change p 49 (some 48)) = d48 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d24 (change p 49 (some 48))) = d48 p
  rw [sub1203, sub1217]
  rfl
theorem sub1245 (p : Pattern) : d49 (change p 49 (some 48)) = d49 p := by
  change (if p 163 then d12 (change p 49 (some 48)) else d48 (change p 49 (some 48))) = d49 p
  rw [sub1203, sub1244]
  rfl
theorem sub1246 (p : Pattern) : d50 (change p 49 (some 48)) = d50 p := by
  change (if p 162 then d49 (change p 49 (some 48)) else d47 (change p 49 (some 48))) = d50 p
  rw [sub1245, sub1243]
  rfl
theorem sub1247 (p : Pattern) : d51 (change p 49 (some 48)) = d51 p := by
  change (if p 161 then d50 (change p 49 (some 48)) else d45 (change p 49 (some 48))) = d51 p
  rw [sub1246, sub1241]
  rfl
theorem sub1248 (p : Pattern) : d52 (change p 49 (some 48)) = d52 p := by
  change (if p 160 then d51 (change p 49 (some 48)) else d29 (change p 49 (some 48))) = d52 p
  rw [sub1247, sub1222]
  rfl
theorem sub1249 (p : Pattern) : d53 (change p 49 (some 48)) = d53 p := by
  change (if p 182 then d32 (change p 49 (some 48)) else d31 (change p 49 (some 48))) = d53 p
  rw [sub1226, sub1225]
  rfl
theorem sub1250 (p : Pattern) : d54 (change p 49 (some 48)) = d54 p := by
  change (if p 163 then d53 (change p 49 (some 48)) else d16 (change p 49 (some 48))) = d54 p
  rw [sub1249, sub1207]
  rfl
theorem sub1251 (p : Pattern) : d55 (change p 49 (some 48)) = d55 p := by
  change (if p 163 then d26 (change p 49 (some 48)) else d20 (change p 49 (some 48))) = d55 p
  rw [sub1219, sub1212]
  rfl
theorem sub1252 (p : Pattern) : d56 (change p 49 (some 48)) = d56 p := by
  change (if p 162 then d55 (change p 49 (some 48)) else d54 (change p 49 (some 48))) = d56 p
  rw [sub1251, sub1250]
  rfl
theorem sub1253 (p : Pattern) : d10 (change p 49 (some 48)) = d10 p := by
  rfl
theorem sub1254 (p : Pattern) : d57 (change p 49 (some 48)) = d57 p := by
  change (if p 247 then d12 (change p 49 (some 48)) else d10 (change p 49 (some 48))) = d57 p
  rw [sub1203, sub1253]
  rfl
theorem sub1255 (p : Pattern) : d58 (change p 49 (some 48)) = d58 p := by
  change (if p 246 then d57 (change p 49 (some 48)) else d10 (change p 49 (some 48))) = d58 p
  rw [sub1254, sub1253]
  rfl
theorem sub1256 (p : Pattern) : d59 (change p 49 (some 48)) = d59 p := by
  change (if p 204 then d12 (change p 49 (some 48)) else d58 (change p 49 (some 48))) = d59 p
  rw [sub1203, sub1255]
  rfl
theorem sub1257 (p : Pattern) : d60 (change p 49 (some 48)) = d60 p := by
  change (if p 182 then d59 (change p 49 (some 48)) else d58 (change p 49 (some 48))) = d60 p
  rw [sub1256, sub1255]
  rfl
theorem sub1258 (p : Pattern) : d61 (change p 49 (some 48)) = d61 p := by
  change (if p 163 then d60 (change p 49 (some 48)) else d20 (change p 49 (some 48))) = d61 p
  rw [sub1257, sub1212]
  rfl
theorem sub1259 (p : Pattern) : d62 (change p 49 (some 48)) = d62 p := by
  change (if p 182 then d41 (change p 49 (some 48)) else d40 (change p 49 (some 48))) = d62 p
  rw [sub1237, sub1236]
  rfl
theorem sub1260 (p : Pattern) : d63 (change p 49 (some 48)) = d63 p := by
  change (if p 163 then d12 (change p 49 (some 48)) else d62 (change p 49 (some 48))) = d63 p
  rw [sub1203, sub1259]
  rfl
theorem sub1261 (p : Pattern) : d64 (change p 49 (some 48)) = d64 p := by
  change (if p 162 then d63 (change p 49 (some 48)) else d61 (change p 49 (some 48))) = d64 p
  rw [sub1260, sub1258]
  rfl
theorem sub1262 (p : Pattern) : d65 (change p 49 (some 48)) = d65 p := by
  change (if p 161 then d64 (change p 49 (some 48)) else d56 (change p 49 (some 48))) = d65 p
  rw [sub1261, sub1252]
  rfl
theorem sub1263 (p : Pattern) : d66 (change p 49 (some 48)) = d66 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d31 (change p 49 (some 48))) = d66 p
  rw [sub1203, sub1225]
  rfl
theorem sub1264 (p : Pattern) : d67 (change p 49 (some 48)) = d67 p := by
  change (if p 163 then d66 (change p 49 (some 48)) else d37 (change p 49 (some 48))) = d67 p
  rw [sub1263, sub1232]
  rfl
theorem sub1265 (p : Pattern) : d68 (change p 49 (some 48)) = d68 p := by
  change (if p 163 then d48 (change p 49 (some 48)) else d43 (change p 49 (some 48))) = d68 p
  rw [sub1244, sub1239]
  rfl
theorem sub1266 (p : Pattern) : d69 (change p 49 (some 48)) = d69 p := by
  change (if p 162 then d68 (change p 49 (some 48)) else d67 (change p 49 (some 48))) = d69 p
  rw [sub1265, sub1264]
  rfl
theorem sub1267 (p : Pattern) : d70 (change p 49 (some 48)) = d70 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d58 (change p 49 (some 48))) = d70 p
  rw [sub1203, sub1255]
  rfl
theorem sub1268 (p : Pattern) : d71 (change p 49 (some 48)) = d71 p := by
  change (if p 163 then d70 (change p 49 (some 48)) else d43 (change p 49 (some 48))) = d71 p
  rw [sub1267, sub1239]
  rfl
theorem sub1269 (p : Pattern) : d72 (change p 49 (some 48)) = d72 p := by
  change (if p 182 then d12 (change p 49 (some 48)) else d40 (change p 49 (some 48))) = d72 p
  rw [sub1203, sub1236]
  rfl
theorem sub1270 (p : Pattern) : d73 (change p 49 (some 48)) = d73 p := by
  change (if p 163 then d12 (change p 49 (some 48)) else d72 (change p 49 (some 48))) = d73 p
  rw [sub1203, sub1269]
  rfl
theorem sub1271 (p : Pattern) : d74 (change p 49 (some 48)) = d74 p := by
  change (if p 162 then d73 (change p 49 (some 48)) else d71 (change p 49 (some 48))) = d74 p
  rw [sub1270, sub1268]
  rfl
theorem sub1272 (p : Pattern) : d75 (change p 49 (some 48)) = d75 p := by
  change (if p 161 then d74 (change p 49 (some 48)) else d69 (change p 49 (some 48))) = d75 p
  rw [sub1271, sub1266]
  rfl
theorem sub1273 (p : Pattern) : d76 (change p 49 (some 48)) = d76 p := by
  change (if p 160 then d75 (change p 49 (some 48)) else d65 (change p 49 (some 48))) = d76 p
  rw [sub1272, sub1262]
  rfl
theorem sub1274 (p : Pattern) : d77 (change p 49 (some 48)) = d77 p := by
  change (if p 141 then d76 (change p 49 (some 48)) else d52 (change p 49 (some 48))) = d77 p
  rw [sub1273, sub1248]
  rfl
theorem sub1275 (p : Pattern) : d78 (change p 49 (some 48)) = d78 p := by
  change (if p 182 then d36 (change p 49 (some 48)) else d35 (change p 49 (some 48))) = d78 p
  rw [sub1231, sub1230]
  rfl
theorem sub1276 (p : Pattern) : d79 (change p 49 (some 48)) = d79 p := by
  change (if p 163 then d78 (change p 49 (some 48)) else d53 (change p 49 (some 48))) = d79 p
  rw [sub1275, sub1249]
  rfl
theorem sub1277 (p : Pattern) : d80 (change p 49 (some 48)) = d80 p := by
  change (if p 162 then d63 (change p 49 (some 48)) else d79 (change p 49 (some 48))) = d80 p
  rw [sub1260, sub1276]
  rfl
theorem sub1278 (p : Pattern) : d81 (change p 49 (some 48)) = d81 p := by
  change (if p 161 then d12 (change p 49 (some 48)) else d80 (change p 49 (some 48))) = d81 p
  rw [sub1203, sub1277]
  rfl
theorem sub1279 (p : Pattern) : d82 (change p 49 (some 48)) = d82 p := by
  change (if p 160 then d81 (change p 49 (some 48)) else d29 (change p 49 (some 48))) = d82 p
  rw [sub1278, sub1222]
  rfl
theorem sub1280 (p : Pattern) : d83 (change p 49 (some 48)) = d83 p := by
  change (if p 163 then d12 (change p 49 (some 48)) else d78 (change p 49 (some 48))) = d83 p
  rw [sub1203, sub1275]
  rfl
theorem sub1281 (p : Pattern) : d84 (change p 49 (some 48)) = d84 p := by
  change (if p 162 then d12 (change p 49 (some 48)) else d83 (change p 49 (some 48))) = d84 p
  rw [sub1203, sub1280]
  rfl
theorem sub1282 (p : Pattern) : d85 (change p 49 (some 48)) = d85 p := by
  change (if p 161 then d12 (change p 49 (some 48)) else d84 (change p 49 (some 48))) = d85 p
  rw [sub1203, sub1281]
  rfl
theorem sub1283 (p : Pattern) : d86 (change p 49 (some 48)) = d86 p := by
  change (if p 160 then d85 (change p 49 (some 48)) else d65 (change p 49 (some 48))) = d86 p
  rw [sub1282, sub1262]
  rfl
theorem sub1284 (p : Pattern) : d87 (change p 49 (some 48)) = d87 p := by
  change (if p 141 then d86 (change p 49 (some 48)) else d82 (change p 49 (some 48))) = d87 p
  rw [sub1283, sub1279]
  rfl
theorem sub1285 (p : Pattern) : d88 (change p 49 (some 48)) = d88 p := by
  change (if p 138 then d87 (change p 49 (some 48)) else d77 (change p 49 (some 48))) = d88 p
  rw [sub1284, sub1274]
  rfl
theorem sub1286 (p : Pattern) : d89 (change p 49 (some 48)) = d89 p := by
  change (if p 163 then d62 (change p 49 (some 48)) else d26 (change p 49 (some 48))) = d89 p
  rw [sub1259, sub1219]
  rfl
theorem sub1287 (p : Pattern) : d90 (change p 49 (some 48)) = d90 p := by
  change (if p 162 then d63 (change p 49 (some 48)) else d89 (change p 49 (some 48))) = d90 p
  rw [sub1260, sub1286]
  rfl
theorem sub1288 (p : Pattern) : d91 (change p 49 (some 48)) = d91 p := by
  change (if p 162 then d12 (change p 49 (some 48)) else d63 (change p 49 (some 48))) = d91 p
  rw [sub1203, sub1260]
  rfl
theorem sub1289 (p : Pattern) : d92 (change p 49 (some 48)) = d92 p := by
  change (if p 161 then d91 (change p 49 (some 48)) else d90 (change p 49 (some 48))) = d92 p
  rw [sub1288, sub1287]
  rfl
theorem sub1290 (p : Pattern) : d93 (change p 49 (some 48)) = d93 p := by
  change (if p 161 then d12 (change p 49 (some 48)) else d91 (change p 49 (some 48))) = d93 p
  rw [sub1203, sub1288]
  rfl
theorem sub1291 (p : Pattern) : d94 (change p 49 (some 48)) = d94 p := by
  change (if p 160 then d93 (change p 49 (some 48)) else d92 (change p 49 (some 48))) = d94 p
  rw [sub1290, sub1289]
  rfl
theorem sub1292 (p : Pattern) : d95 (change p 49 (some 48)) = d95 p := by
  change (if p 160 then d12 (change p 49 (some 48)) else d93 (change p 49 (some 48))) = d95 p
  rw [sub1203, sub1290]
  rfl
theorem sub1293 (p : Pattern) : d96 (change p 49 (some 48)) = d96 p := by
  change (if p 141 then d95 (change p 49 (some 48)) else d94 (change p 49 (some 48))) = d96 p
  rw [sub1292, sub1291]
  rfl
theorem sub1294 (p : Pattern) : d97 (change p 49 (some 48)) = d97 p := by
  change (if p 138 then d96 (change p 49 (some 48)) else d87 (change p 49 (some 48))) = d97 p
  rw [sub1293, sub1284]
  rfl
theorem sub1295 (p : Pattern) : d98 (change p 49 (some 48)) = d98 p := by
  change (if p 116 then d97 (change p 49 (some 48)) else d88 (change p 49 (some 48))) = d98 p
  rw [sub1294, sub1285]
  rfl
theorem sub1296 (p : Pattern) : d99 (change p 49 (some 48)) = d99 p := by
  change (if p 138 then d12 (change p 49 (some 48)) else d87 (change p 49 (some 48))) = d99 p
  rw [sub1203, sub1284]
  rfl
theorem sub1297 (p : Pattern) : d100 (change p 49 (some 48)) = d100 p := by
  change (if p 116 then d99 (change p 49 (some 48)) else d88 (change p 49 (some 48))) = d100 p
  rw [sub1296, sub1285]
  rfl
theorem sub1298 (p : Pattern) : d101 (change p 49 (some 48)) = d101 p := by
  change (if p 115 then d100 (change p 49 (some 48)) else d98 (change p 49 (some 48))) = d101 p
  rw [sub1297, sub1295]
  rfl
theorem sub1299 (p : Pattern) : d483 (change p 49 (some 48)) = d101 p := by
  change d101 (change p 49 (some 48)) = d101 p
  exact sub1298 p
theorem sub1300 (p : Pattern) : d484 (change p 49 (some 48)) = d101 p := by
  change d483 (change p 49 (some 48)) = d101 p
  exact sub1299 p
theorem sub1301 (p : Pattern) : d0 (change p 10000 (some 49)) = d0 p := by
  rfl
theorem sub1302 (p : Pattern) : d12 (change p 10000 (some 49)) = d12 p := by
  rfl
theorem sub1303 (p : Pattern) : d13 (change p 10000 (some 49)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d0 (change p 10000 (some 49))) = d13 p
  rw [sub1302, sub1301]
  rfl
theorem sub1304 (p : Pattern) : d14 (change p 10000 (some 49)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 49)) else d0 (change p 10000 (some 49))) = d14 p
  rw [sub1303, sub1301]
  rfl
theorem sub1305 (p : Pattern) : d15 (change p 10000 (some 49)) = d15 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d15 p
  rw [sub1302, sub1304]
  rfl
theorem sub1306 (p : Pattern) : d16 (change p 10000 (some 49)) = d16 p := by
  change (if p 182 then d15 (change p 10000 (some 49)) else d14 (change p 10000 (some 49))) = d16 p
  rw [sub1305, sub1304]
  rfl
theorem sub1307 (p : Pattern) : d4 (change p 10000 (some 49)) = d4 p := by
  rfl
theorem sub1308 (p : Pattern) : d17 (change p 10000 (some 49)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d4 (change p 10000 (some 49))) = d17 p
  rw [sub1302, sub1307]
  rfl
theorem sub1309 (p : Pattern) : d18 (change p 10000 (some 49)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 49)) else d4 (change p 10000 (some 49))) = d18 p
  rw [sub1308, sub1307]
  rfl
theorem sub1310 (p : Pattern) : d19 (change p 10000 (some 49)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d18 (change p 10000 (some 49))) = d19 p
  rw [sub1302, sub1309]
  rfl
theorem sub1311 (p : Pattern) : d20 (change p 10000 (some 49)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 49)) else d18 (change p 10000 (some 49))) = d20 p
  rw [sub1310, sub1309]
  rfl
theorem sub1312 (p : Pattern) : d21 (change p 10000 (some 49)) = d21 p := by
  change (if p 163 then d20 (change p 10000 (some 49)) else d16 (change p 10000 (some 49))) = d21 p
  rw [sub1311, sub1306]
  rfl
theorem sub1313 (p : Pattern) : d22 (change p 10000 (some 49)) = d22 p := by
  change (if p 162 then d21 (change p 10000 (some 49)) else d16 (change p 10000 (some 49))) = d22 p
  rw [sub1312, sub1306]
  rfl
theorem sub1314 (p : Pattern) : d9 (change p 10000 (some 49)) = d9 p := by
  rfl
theorem sub1315 (p : Pattern) : d23 (change p 10000 (some 49)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 49)) else d9 (change p 10000 (some 49))) = d23 p
  rw [sub1302, sub1314]
  rfl
theorem sub1316 (p : Pattern) : d24 (change p 10000 (some 49)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 49)) else d9 (change p 10000 (some 49))) = d24 p
  rw [sub1315, sub1314]
  rfl
theorem sub1317 (p : Pattern) : d25 (change p 10000 (some 49)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 49)) else d24 (change p 10000 (some 49))) = d25 p
  rw [sub1302, sub1316]
  rfl
theorem sub1318 (p : Pattern) : d26 (change p 10000 (some 49)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 49)) else d24 (change p 10000 (some 49))) = d26 p
  rw [sub1317, sub1316]
  rfl
theorem sub1319 (p : Pattern) : d27 (change p 10000 (some 49)) = d27 p := by
  change (if p 163 then d12 (change p 10000 (some 49)) else d26 (change p 10000 (some 49))) = d27 p
  rw [sub1302, sub1318]
  rfl
end NetHack.Sokoban22Refined85
