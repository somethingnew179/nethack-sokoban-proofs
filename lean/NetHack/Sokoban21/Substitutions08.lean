/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions07
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1200 (pattern : Twelve) : d1279 (change pattern 7 8) = d1276 pattern := by
  change d1276 (change pattern 7 8) = d1276 pattern
  exact s1199 pattern
theorem s1201 (pattern : Twelve) : d1382 (change pattern 7 8) = d1276 pattern := by
  change d1279 (change pattern 7 8) = d1276 pattern
  exact s1200 pattern
theorem s1202 (pattern : Twelve) : d1387 (change pattern 7 8) = d1978 pattern := by
  change (if pattern.f then d1382 (change pattern 7 8) else d241 (change pattern 7 8)) = d1978 pattern
  rw [s1201, s1070]
  rfl
theorem s1203 (pattern : Twelve) : d1388 (change pattern 7 8) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d942 (change pattern 7 8)) = d1650 pattern
  rw [s1108, s1146]
  rfl
theorem s1204 (pattern : Twelve) : d1394 (change pattern 7 8) = d1979 pattern := by
  change (if pattern.e then d1388 (change pattern 7 8) else d1387 (change pattern 7 8)) = d1979 pattern
  rw [s1203, s1202]
  rfl
theorem s1205 (pattern : Twelve) : d1398 (change pattern 7 8) = d1980 pattern := by
  change (if pattern.j then d1394 (change pattern 7 8) else d1393 (change pattern 7 8)) = d1980 pattern
  rw [s1204, s1197]
  rfl
theorem s1206 (pattern : Twelve) : d1389 (change pattern 7 8) = d1976 pattern := by
  change (if pattern.f then d1380 (change pattern 7 8) else d944 (change pattern 7 8)) = d1976 pattern
  rw [s1190, s1154]
  rfl
theorem s1207 (pattern : Twelve) : d1395 (change pattern 7 8) = d1977 pattern := by
  change (if pattern.e then d1386 (change pattern 7 8) else d1389 (change pattern 7 8)) = d1977 pattern
  rw [s1196, s1206]
  rfl
theorem s1208 (pattern : Twelve) : d1399 (change pattern 7 8) = d1980 pattern := by
  change (if pattern.j then d1394 (change pattern 7 8) else d1395 (change pattern 7 8)) = d1980 pattern
  rw [s1204, s1207]
  rfl
theorem s1209 (pattern : Twelve) : d1403 (change pattern 7 8) = d1980 pattern := by
  change (if pattern.d then d1399 (change pattern 7 8) else d1398 (change pattern 7 8)) = d1980 pattern
  rw [s1208, s1205]
  simp only [ite_self]
theorem s1210 (pattern : Twelve) : d1277 (change pattern 7 8) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 7 8) else d15 (change pattern 7 8)) = d1277 pattern
  rw [s1162, s1098]
  rfl
theorem s1211 (pattern : Twelve) : d1282 (change pattern 7 8) = d1277 pattern := by
  change d1277 (change pattern 7 8) = d1277 pattern
  exact s1210 pattern
theorem s1212 (pattern : Twelve) : d1383 (change pattern 7 8) = d1277 pattern := by
  change d1282 (change pattern 7 8) = d1277 pattern
  exact s1211 pattern
theorem s1213 (pattern : Twelve) : d1390 (change pattern 7 8) = d1981 pattern := by
  change (if pattern.f then d1383 (change pattern 7 8) else d251 (change pattern 7 8)) = d1981 pattern
  rw [s1212, s1101]
  rfl
theorem s1214 (pattern : Twelve) : d1391 (change pattern 7 8) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d945 (change pattern 7 8)) = d1815 pattern
  rw [s1108, s1165]
  rfl
theorem s1215 (pattern : Twelve) : d1396 (change pattern 7 8) = d1982 pattern := by
  change (if pattern.e then d1391 (change pattern 7 8) else d1390 (change pattern 7 8)) = d1982 pattern
  rw [s1214, s1213]
  rfl
theorem s1216 (pattern : Twelve) : d1400 (change pattern 7 8) = d1983 pattern := by
  change (if pattern.j then d1396 (change pattern 7 8) else d1394 (change pattern 7 8)) = d1983 pattern
  rw [s1215, s1204]
  rfl
theorem s1217 (pattern : Twelve) : d1401 (change pattern 7 8) = d1984 pattern := by
  change (if pattern.j then d6 (change pattern 7 8) else d1394 (change pattern 7 8)) = d1984 pattern
  rw [s1108, s1204]
  rfl
theorem s1218 (pattern : Twelve) : d1404 (change pattern 7 8) = d1985 pattern := by
  change (if pattern.d then d1401 (change pattern 7 8) else d1400 (change pattern 7 8)) = d1985 pattern
  rw [s1217, s1216]
  rfl
theorem s1219 (pattern : Twelve) : d1405 (change pattern 7 8) = d1986 pattern := by
  change (if pattern.c then d1404 (change pattern 7 8) else d1403 (change pattern 7 8)) = d1986 pattern
  rw [s1218, s1209]
  rfl
theorem s1220 (pattern : Twelve) : d1283 (change pattern 7 8) = d23 pattern := by
  change d23 (change pattern 7 8) = d23 pattern
  exact s1068 pattern
theorem s1221 (pattern : Twelve) : d1384 (change pattern 7 8) = d23 pattern := by
  change d1283 (change pattern 7 8) = d23 pattern
  exact s1220 pattern
theorem s1222 (pattern : Twelve) : d1392 (change pattern 7 8) = d1987 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d1384 (change pattern 7 8)) = d1987 pattern
  rw [s1108, s1221]
  rfl
theorem s1223 (pattern : Twelve) : d1397 (change pattern 7 8) = d1988 pattern := by
  change (if pattern.e then d1392 (change pattern 7 8) else d1389 (change pattern 7 8)) = d1988 pattern
  rw [s1222, s1206]
  rfl
theorem s1224 (pattern : Twelve) : d1402 (change pattern 7 8) = d1989 pattern := by
  change (if pattern.j then d1394 (change pattern 7 8) else d1397 (change pattern 7 8)) = d1989 pattern
  rw [s1204, s1223]
  rfl
theorem s1225 (pattern : Twelve) : d1406 (change pattern 7 8) = d1990 pattern := by
  change (if pattern.c then d1404 (change pattern 7 8) else d1402 (change pattern 7 8)) = d1990 pattern
  rw [s1218, s1224]
  rfl
theorem s1226 (pattern : Twelve) : d1408 (change pattern 7 8) = d1991 pattern := by
  change (if pattern.g then d1406 (change pattern 7 8) else d1405 (change pattern 7 8)) = d1991 pattern
  rw [s1225, s1219]
  rfl
theorem s1227 (pattern : Twelve) : d1407 (change pattern 7 8) = d1986 pattern := by
  change (if pattern.c then d1404 (change pattern 7 8) else d1399 (change pattern 7 8)) = d1986 pattern
  rw [s1218, s1208]
  rfl
theorem s1228 (pattern : Twelve) : d1409 (change pattern 7 8) = d1991 pattern := by
  change (if pattern.g then d1406 (change pattern 7 8) else d1407 (change pattern 7 8)) = d1991 pattern
  rw [s1225, s1227]
  rfl
theorem s1229 (pattern : Twelve) : d1410 (change pattern 7 8) = d1991 pattern := by
  change (if pattern.b then d1409 (change pattern 7 8) else d1408 (change pattern 7 8)) = d1991 pattern
  rw [s1228, s1226]
  simp only [ite_self]
theorem s1230 (pattern : Twelve) : d1411 (change pattern 7 8) = d1991 pattern := by
  change (if pattern.a then d1409 (change pattern 7 8) else d1410 (change pattern 7 8)) = d1991 pattern
  rw [s1228, s1229]
  simp only [ite_self]
theorem s1231 (pattern : Twelve) : d1324 (change pattern 7 8) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 7 8) else d11 (change pattern 7 8)) = d1324 pattern
  rw [s1142, s1193]
  rfl
theorem s1232 (pattern : Twelve) : d1689 (change pattern 7 8) = d1324 pattern := by
  change d1324 (change pattern 7 8) = d1324 pattern
  exact s1231 pattern
theorem s1233 (pattern : Twelve) : d1693 (change pattern 7 8) = d1649 pattern := by
  change (if pattern.f then d1689 (change pattern 7 8) else d1381 (change pattern 7 8)) = d1649 pattern
  rw [s1232, s1195]
  rfl
theorem s1234 (pattern : Twelve) : d1690 (change pattern 7 8) = d25 pattern := by
  change d25 (change pattern 7 8) = d25 pattern
  exact s1144 pattern
theorem s1235 (pattern : Twelve) : d1694 (change pattern 7 8) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d1690 (change pattern 7 8)) = d1650 pattern
  rw [s1108, s1234]
  rfl
theorem s1236 (pattern : Twelve) : d1697 (change pattern 7 8) = d1656 pattern := by
  change (if pattern.e then d1694 (change pattern 7 8) else d1693 (change pattern 7 8)) = d1656 pattern
  rw [s1235, s1233]
  rfl
theorem s1237 (pattern : Twelve) : d20 (change pattern 7 8) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 7 8) else d12 (change pattern 7 8)) = d20 pattern
  rw [s1161, s1143]
  rfl
theorem s1238 (pattern : Twelve) : d1644 (change pattern 7 8) = d20 pattern := by
  change d20 (change pattern 7 8) = d20 pattern
  exact s1237 pattern
theorem s1239 (pattern : Twelve) : d1691 (change pattern 7 8) = d20 pattern := by
  change d1644 (change pattern 7 8) = d20 pattern
  exact s1238 pattern
theorem s1240 (pattern : Twelve) : d1695 (change pattern 7 8) = d1814 pattern := by
  change (if pattern.f then d1691 (change pattern 7 8) else d942 (change pattern 7 8)) = d1814 pattern
  rw [s1239, s1146]
  rfl
theorem s1241 (pattern : Twelve) : d1698 (change pattern 7 8) = d1818 pattern := by
  change (if pattern.e then d1391 (change pattern 7 8) else d1695 (change pattern 7 8)) = d1818 pattern
  rw [s1214, s1240]
  rfl
theorem s1242 (pattern : Twelve) : d1700 (change pattern 7 8) = d1992 pattern := by
  change (if pattern.j then d1698 (change pattern 7 8) else d1697 (change pattern 7 8)) = d1992 pattern
  rw [s1241, s1236]
  rfl
theorem s1243 (pattern : Twelve) : d22 (change pattern 7 8) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 7 8) else d14 (change pattern 7 8)) = d22 pattern
  rw [s1108, s1162]
  rfl
theorem s1244 (pattern : Twelve) : d1646 (change pattern 7 8) = d22 pattern := by
  change d22 (change pattern 7 8) = d22 pattern
  exact s1243 pattern
theorem s1245 (pattern : Twelve) : d1692 (change pattern 7 8) = d22 pattern := by
  change d1646 (change pattern 7 8) = d22 pattern
  exact s1244 pattern
theorem s1246 (pattern : Twelve) : d1696 (change pattern 7 8) = d1993 pattern := by
  change (if pattern.f then d1692 (change pattern 7 8) else d945 (change pattern 7 8)) = d1993 pattern
  rw [s1245, s1165]
  rfl
theorem s1247 (pattern : Twelve) : d822 (change pattern 7 8) = d6 pattern := by
  change d6 (change pattern 7 8) = d6 pattern
  exact s1108 pattern
theorem s1248 (pattern : Twelve) : d1252 (change pattern 7 8) = d6 pattern := by
  change d822 (change pattern 7 8) = d6 pattern
  exact s1247 pattern
theorem s1249 (pattern : Twelve) : d1626 (change pattern 7 8) = d6 pattern := by
  change (if pattern.f then d6 (change pattern 7 8) else d1252 (change pattern 7 8)) = d6 pattern
  rw [s1108, s1248]
  simp only [ite_self]
theorem s1250 (pattern : Twelve) : d1699 (change pattern 7 8) = d1994 pattern := by
  change (if pattern.e then d1626 (change pattern 7 8) else d1696 (change pattern 7 8)) = d1994 pattern
  rw [s1249, s1246]
  rfl
theorem s1251 (pattern : Twelve) : d1701 (change pattern 7 8) = d1995 pattern := by
  change (if pattern.j then d1699 (change pattern 7 8) else d1698 (change pattern 7 8)) = d1995 pattern
  rw [s1250, s1241]
  rfl
theorem s1252 (pattern : Twelve) : d1702 (change pattern 7 8) = d1996 pattern := by
  change (if pattern.j then d6 (change pattern 7 8) else d1698 (change pattern 7 8)) = d1996 pattern
  rw [s1108, s1241]
  rfl
theorem s1253 (pattern : Twelve) : d1703 (change pattern 7 8) = d1997 pattern := by
  change (if pattern.d then d1702 (change pattern 7 8) else d1701 (change pattern 7 8)) = d1997 pattern
  rw [s1252, s1251]
  rfl
theorem s1254 (pattern : Twelve) : d1704 (change pattern 7 8) = d1998 pattern := by
  change (if pattern.c then d1703 (change pattern 7 8) else d1700 (change pattern 7 8)) = d1998 pattern
  rw [s1253, s1242]
  rfl
theorem s1255 (pattern : Twelve) : d0 (change pattern 4 12) = d0 pattern := by
  rfl
theorem s1256 (pattern : Twelve) : d1 (change pattern 4 12) = d1 pattern := by
  rfl
theorem s1257 (pattern : Twelve) : d7 (change pattern 4 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 4 12) else d0 (change pattern 4 12)) = d7 pattern
  rw [s1256, s1255]
  rfl
theorem s1258 (pattern : Twelve) : d17 (change pattern 4 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 4 12) else d0 (change pattern 4 12)) = d17 pattern
  rw [s1257, s1255]
  rfl
theorem s1259 (pattern : Twelve) : d27 (change pattern 4 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 4 12) else d17 (change pattern 4 12)) = d27 pattern
  rw [s1256, s1258]
  rfl
theorem s1260 (pattern : Twelve) : d814 (change pattern 4 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 4 12) else d7 (change pattern 4 12)) = d814 pattern
  rw [s1256, s1257]
  rfl
theorem s1261 (pattern : Twelve) : d816 (change pattern 4 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 4 12) else d814 (change pattern 4 12)) = d816 pattern
  rw [s1256, s1260]
  rfl
theorem s1262 (pattern : Twelve) : d824 (change pattern 4 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 4 12) else d27 (change pattern 4 12)) = d824 pattern
  rw [s1261, s1259]
  rfl
theorem s1263 (pattern : Twelve) : d838 (change pattern 4 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 4 12) else d0 (change pattern 4 12)) = d838 pattern
  rw [s1262, s1255]
  rfl
theorem s1264 (pattern : Twelve) : d980 (change pattern 4 12) = d838 pattern := by
  change d838 (change pattern 4 12) = d838 pattern
  exact s1263 pattern
theorem s1265 (pattern : Twelve) : d2 (change pattern 4 12) = d2 pattern := by
  rfl
theorem s1266 (pattern : Twelve) : d30 (change pattern 4 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 4 12) else d0 (change pattern 4 12)) = d30 pattern
  rw [s1265, s1255]
  rfl
theorem s1267 (pattern : Twelve) : d6 (change pattern 4 12) = d6 pattern := by
  rfl
theorem s1268 (pattern : Twelve) : d35 (change pattern 4 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d0 (change pattern 4 12)) = d35 pattern
  rw [s1267, s1255]
  rfl
theorem s1269 (pattern : Twelve) : d56 (change pattern 4 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 4 12) else d30 (change pattern 4 12)) = d56 pattern
  rw [s1268, s1266]
  rfl
theorem s1270 (pattern : Twelve) : d3 (change pattern 4 12) = d3 pattern := by
  rfl
theorem s1271 (pattern : Twelve) : d9 (change pattern 4 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 4 12) else d2 (change pattern 4 12)) = d9 pattern
  rw [s1270, s1265]
  rfl
theorem s1272 (pattern : Twelve) : d23 (change pattern 4 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 4 12) else d2 (change pattern 4 12)) = d23 pattern
  rw [s1271, s1265]
  rfl
theorem s1273 (pattern : Twelve) : d34 (change pattern 4 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 4 12) else d17 (change pattern 4 12)) = d34 pattern
  rw [s1272, s1258]
  rfl
theorem s1274 (pattern : Twelve) : d818 (change pattern 4 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d814 (change pattern 4 12)) = d818 pattern
  rw [s1267, s1260]
  rfl
theorem s1275 (pattern : Twelve) : d826 (change pattern 4 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 4 12) else d34 (change pattern 4 12)) = d826 pattern
  rw [s1274, s1273]
  rfl
theorem s1276 (pattern : Twelve) : d840 (change pattern 4 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 4 12) else d56 (change pattern 4 12)) = d840 pattern
  rw [s1275, s1269]
  rfl
theorem s1277 (pattern : Twelve) : d981 (change pattern 4 12) = d840 pattern := by
  change d840 (change pattern 4 12) = d840 pattern
  exact s1276 pattern
theorem s1278 (pattern : Twelve) : d991 (change pattern 4 12) = d2000 pattern := by
  change (if pattern.j then d981 (change pattern 4 12) else d980 (change pattern 4 12)) = d2000 pattern
  rw [s1277, s1264]
  rfl
theorem s1279 (pattern : Twelve) : d982 (change pattern 4 12) = d838 pattern := by
  change d838 (change pattern 4 12) = d838 pattern
  exact s1263 pattern
theorem s1280 (pattern : Twelve) : d983 (change pattern 4 12) = d840 pattern := by
  change d840 (change pattern 4 12) = d840 pattern
  exact s1276 pattern
theorem s1281 (pattern : Twelve) : d992 (change pattern 4 12) = d2000 pattern := by
  change (if pattern.j then d983 (change pattern 4 12) else d982 (change pattern 4 12)) = d2000 pattern
  rw [s1280, s1279]
  rfl
theorem s1282 (pattern : Twelve) : d1000 (change pattern 4 12) = d2000 pattern := by
  change (if pattern.d then d992 (change pattern 4 12) else d991 (change pattern 4 12)) = d2000 pattern
  rw [s1281, s1278]
  simp only [ite_self]
theorem s1283 (pattern : Twelve) : d819 (change pattern 4 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 4 12) else d814 (change pattern 4 12)) = d819 pattern
  rw [s1270, s1260]
  rfl
theorem s1284 (pattern : Twelve) : d828 (change pattern 4 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 4 12) else d34 (change pattern 4 12)) = d828 pattern
  rw [s1283, s1273]
  rfl
theorem s1285 (pattern : Twelve) : d842 (change pattern 4 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 4 12) else d30 (change pattern 4 12)) = d842 pattern
  rw [s1284, s1266]
  rfl
theorem s1286 (pattern : Twelve) : d984 (change pattern 4 12) = d842 pattern := by
  change d842 (change pattern 4 12) = d842 pattern
  exact s1285 pattern
theorem s1287 (pattern : Twelve) : d4 (change pattern 4 12) = d4 pattern := by
  rfl
theorem s1288 (pattern : Twelve) : d38 (change pattern 4 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 4 12) else d2 (change pattern 4 12)) = d38 pattern
  rw [s1287, s1265]
  rfl
theorem s1289 (pattern : Twelve) : d39 (change pattern 4 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d2 (change pattern 4 12)) = d39 pattern
  rw [s1267, s1265]
  rfl
theorem s1290 (pattern : Twelve) : d59 (change pattern 4 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 4 12) else d38 (change pattern 4 12)) = d59 pattern
  rw [s1289, s1288]
  rfl
theorem s1291 (pattern : Twelve) : d5 (change pattern 4 12) = d5 pattern := by
  rfl
theorem s1292 (pattern : Twelve) : d15 (change pattern 4 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 4 12) else d4 (change pattern 4 12)) = d15 pattern
  rw [s1291, s1287]
  rfl
theorem s1293 (pattern : Twelve) : d24 (change pattern 4 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 4 12) else d4 (change pattern 4 12)) = d24 pattern
  rw [s1292, s1287]
  rfl
theorem s1294 (pattern : Twelve) : d41 (change pattern 4 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 4 12) else d23 (change pattern 4 12)) = d41 pattern
  rw [s1293, s1272]
  rfl
theorem s1295 (pattern : Twelve) : d815 (change pattern 4 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 4 12) else d9 (change pattern 4 12)) = d815 pattern
  rw [s1270, s1271]
  rfl
theorem s1296 (pattern : Twelve) : d820 (change pattern 4 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d815 (change pattern 4 12)) = d820 pattern
  rw [s1267, s1295]
  rfl
theorem s1297 (pattern : Twelve) : d829 (change pattern 4 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 4 12) else d41 (change pattern 4 12)) = d829 pattern
  rw [s1296, s1294]
  rfl
theorem s1298 (pattern : Twelve) : d844 (change pattern 4 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 4 12) else d59 (change pattern 4 12)) = d844 pattern
  rw [s1297, s1290]
  rfl
theorem s1299 (pattern : Twelve) : d985 (change pattern 4 12) = d844 pattern := by
  change d844 (change pattern 4 12) = d844 pattern
  exact s1298 pattern
theorem s1300 (pattern : Twelve) : d993 (change pattern 4 12) = d2001 pattern := by
  change (if pattern.j then d985 (change pattern 4 12) else d984 (change pattern 4 12)) = d2001 pattern
  rw [s1299, s1286]
  rfl
theorem s1301 (pattern : Twelve) : d994 (change pattern 4 12) = d2002 pattern := by
  change (if pattern.j then d6 (change pattern 4 12) else d983 (change pattern 4 12)) = d2002 pattern
  rw [s1267, s1280]
  rfl
theorem s1302 (pattern : Twelve) : d1001 (change pattern 4 12) = d2003 pattern := by
  change (if pattern.d then d994 (change pattern 4 12) else d993 (change pattern 4 12)) = d2003 pattern
  rw [s1301, s1300]
  rfl
theorem s1303 (pattern : Twelve) : d1004 (change pattern 4 12) = d2004 pattern := by
  change (if pattern.c then d1001 (change pattern 4 12) else d1000 (change pattern 4 12)) = d2004 pattern
  rw [s1302, s1282]
  rfl
theorem s1304 (pattern : Twelve) : d986 (change pattern 4 12) = d838 pattern := by
  change d838 (change pattern 4 12) = d838 pattern
  exact s1263 pattern
theorem s1305 (pattern : Twelve) : d45 (change pattern 4 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d1 (change pattern 4 12)) = d45 pattern
  rw [s1267, s1256]
  rfl
theorem s1306 (pattern : Twelve) : d832 (change pattern 4 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 4 12) else d34 (change pattern 4 12)) = d832 pattern
  rw [s1305, s1273]
  rfl
theorem s1307 (pattern : Twelve) : d847 (change pattern 4 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 4 12) else d56 (change pattern 4 12)) = d847 pattern
  rw [s1306, s1269]
  rfl
theorem s1308 (pattern : Twelve) : d987 (change pattern 4 12) = d847 pattern := by
  change d847 (change pattern 4 12) = d847 pattern
  exact s1307 pattern
theorem s1309 (pattern : Twelve) : d995 (change pattern 4 12) = d2005 pattern := by
  change (if pattern.j then d987 (change pattern 4 12) else d986 (change pattern 4 12)) = d2005 pattern
  rw [s1308, s1304]
  rfl
theorem s1310 (pattern : Twelve) : d46 (change pattern 4 12) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 4 12) else d1 (change pattern 4 12)) = d46 pattern
  rw [s1270, s1256]
  rfl
theorem s1311 (pattern : Twelve) : d834 (change pattern 4 12) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 4 12) else d34 (change pattern 4 12)) = d834 pattern
  rw [s1310, s1273]
  rfl
theorem s1312 (pattern : Twelve) : d849 (change pattern 4 12) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 4 12) else d30 (change pattern 4 12)) = d849 pattern
  rw [s1311, s1266]
  rfl
theorem s1313 (pattern : Twelve) : d988 (change pattern 4 12) = d849 pattern := by
  change d849 (change pattern 4 12) = d849 pattern
  exact s1312 pattern
theorem s1314 (pattern : Twelve) : d47 (change pattern 4 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d3 (change pattern 4 12)) = d47 pattern
  rw [s1267, s1270]
  rfl
theorem s1315 (pattern : Twelve) : d836 (change pattern 4 12) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 4 12) else d41 (change pattern 4 12)) = d836 pattern
  rw [s1314, s1294]
  rfl
theorem s1316 (pattern : Twelve) : d851 (change pattern 4 12) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 4 12) else d59 (change pattern 4 12)) = d851 pattern
  rw [s1315, s1290]
  rfl
theorem s1317 (pattern : Twelve) : d989 (change pattern 4 12) = d851 pattern := by
  change d851 (change pattern 4 12) = d851 pattern
  exact s1316 pattern
theorem s1318 (pattern : Twelve) : d996 (change pattern 4 12) = d2006 pattern := by
  change (if pattern.j then d989 (change pattern 4 12) else d988 (change pattern 4 12)) = d2006 pattern
  rw [s1317, s1313]
  rfl
theorem s1319 (pattern : Twelve) : d997 (change pattern 4 12) = d2007 pattern := by
  change (if pattern.j then d6 (change pattern 4 12) else d987 (change pattern 4 12)) = d2007 pattern
  rw [s1267, s1308]
  rfl
theorem s1320 (pattern : Twelve) : d1002 (change pattern 4 12) = d2008 pattern := by
  change (if pattern.d then d997 (change pattern 4 12) else d996 (change pattern 4 12)) = d2008 pattern
  rw [s1319, s1318]
  rfl
theorem s1321 (pattern : Twelve) : d1005 (change pattern 4 12) = d2009 pattern := by
  change (if pattern.c then d1002 (change pattern 4 12) else d995 (change pattern 4 12)) = d2009 pattern
  rw [s1320, s1309]
  rfl
theorem s1322 (pattern : Twelve) : d1007 (change pattern 4 12) = d2010 pattern := by
  change (if pattern.g then d1005 (change pattern 4 12) else d1004 (change pattern 4 12)) = d2010 pattern
  rw [s1321, s1303]
  rfl
theorem s1323 (pattern : Twelve) : d998 (change pattern 4 12) = d2000 pattern := by
  change (if pattern.j then d983 (change pattern 4 12) else d986 (change pattern 4 12)) = d2000 pattern
  rw [s1280, s1304]
  rfl
theorem s1324 (pattern : Twelve) : d990 (change pattern 4 12) = d842 pattern := by
  change d842 (change pattern 4 12) = d842 pattern
  exact s1285 pattern
theorem s1325 (pattern : Twelve) : d999 (change pattern 4 12) = d2001 pattern := by
  change (if pattern.j then d985 (change pattern 4 12) else d990 (change pattern 4 12)) = d2001 pattern
  rw [s1299, s1324]
  rfl
theorem s1326 (pattern : Twelve) : d1003 (change pattern 4 12) = d2003 pattern := by
  change (if pattern.d then d994 (change pattern 4 12) else d999 (change pattern 4 12)) = d2003 pattern
  rw [s1301, s1325]
  rfl
theorem s1327 (pattern : Twelve) : d1006 (change pattern 4 12) = d2004 pattern := by
  change (if pattern.c then d1003 (change pattern 4 12) else d998 (change pattern 4 12)) = d2004 pattern
  rw [s1326, s1323]
  rfl
theorem s1328 (pattern : Twelve) : d1008 (change pattern 4 12) = d2010 pattern := by
  change (if pattern.g then d1005 (change pattern 4 12) else d1006 (change pattern 4 12)) = d2010 pattern
  rw [s1321, s1327]
  rfl
theorem s1329 (pattern : Twelve) : d1009 (change pattern 4 12) = d2010 pattern := by
  change (if pattern.b then d1008 (change pattern 4 12) else d1007 (change pattern 4 12)) = d2010 pattern
  rw [s1328, s1322]
  simp only [ite_self]
theorem s1330 (pattern : Twelve) : d1010 (change pattern 4 12) = d2010 pattern := by
  change (if pattern.a then d1008 (change pattern 4 12) else d1009 (change pattern 4 12)) = d2010 pattern
  rw [s1328, s1329]
  simp only [ite_self]
theorem s1331 (pattern : Twelve) : d8 (change pattern 4 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 4 12) else d1 (change pattern 4 12)) = d8 pattern
  rw [s1265, s1256]
  rfl
theorem s1332 (pattern : Twelve) : d1275 (change pattern 4 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 4 12) else d7 (change pattern 4 12)) = d1275 pattern
  rw [s1331, s1257]
  rfl
theorem s1333 (pattern : Twelve) : d872 (change pattern 4 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 4 12) else d1 (change pattern 4 12)) = d872 pattern
  rw [s1331, s1256]
  rfl
theorem s1334 (pattern : Twelve) : d1278 (change pattern 4 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 4 12) else d1275 (change pattern 4 12)) = d1278 pattern
  rw [s1333, s1332]
  rfl
theorem s1335 (pattern : Twelve) : d1284 (change pattern 4 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 4 12) else d1278 (change pattern 4 12)) = d1284 pattern
  rw [s1333, s1334]
  rfl
theorem s1336 (pattern : Twelve) : d1293 (change pattern 4 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 4 12) else d17 (change pattern 4 12)) = d1293 pattern
  rw [s1335, s1258]
  rfl
theorem s1337 (pattern : Twelve) : d1412 (change pattern 4 12) = d1293 pattern := by
  change d1293 (change pattern 4 12) = d1293 pattern
  exact s1336 pattern
theorem s1338 (pattern : Twelve) : d36 (change pattern 4 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d17 (change pattern 4 12)) = d36 pattern
  rw [s1267, s1258]
  rfl
theorem s1339 (pattern : Twelve) : d827 (change pattern 4 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 4 12) else d34 (change pattern 4 12)) = d827 pattern
  rw [s1338, s1273]
  rfl
theorem s1340 (pattern : Twelve) : d117 (change pattern 4 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 4 12) else d3 (change pattern 4 12)) = d117 pattern
  rw [s1287, s1270]
  rfl
theorem s1341 (pattern : Twelve) : d1276 (change pattern 4 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 4 12) else d9 (change pattern 4 12)) = d1276 pattern
  rw [s1340, s1271]
  rfl
theorem s1342 (pattern : Twelve) : d1279 (change pattern 4 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 4 12) else d1275 (change pattern 4 12)) = d1279 pattern
  rw [s1341, s1332]
  rfl
theorem s1343 (pattern : Twelve) : d1280 (change pattern 4 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 4 12) else d872 (change pattern 4 12)) = d1280 pattern
  rw [s1267, s1333]
  rfl
theorem s1344 (pattern : Twelve) : d1285 (change pattern 4 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 4 12) else d1279 (change pattern 4 12)) = d1285 pattern
  rw [s1343, s1342]
  rfl
theorem s1345 (pattern : Twelve) : d1295 (change pattern 4 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 4 12) else d827 (change pattern 4 12)) = d1295 pattern
  rw [s1344, s1339]
  rfl
theorem s1346 (pattern : Twelve) : d1413 (change pattern 4 12) = d1295 pattern := by
  change d1295 (change pattern 4 12) = d1295 pattern
  exact s1345 pattern
theorem s1347 (pattern : Twelve) : d1417 (change pattern 4 12) = d2011 pattern := by
  change (if pattern.j then d1413 (change pattern 4 12) else d1412 (change pattern 4 12)) = d2011 pattern
  rw [s1346, s1337]
  rfl
theorem s1348 (pattern : Twelve) : d1414 (change pattern 4 12) = d1293 pattern := by
  change d1293 (change pattern 4 12) = d1293 pattern
  exact s1336 pattern
theorem s1349 (pattern : Twelve) : d1418 (change pattern 4 12) = d2011 pattern := by
  change (if pattern.j then d1413 (change pattern 4 12) else d1414 (change pattern 4 12)) = d2011 pattern
  rw [s1346, s1348]
  rfl
end NetHack.Sokoban21.Diagram
