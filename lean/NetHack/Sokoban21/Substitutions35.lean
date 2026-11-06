/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions34
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5250 (pattern : Twelve) : d881 (change pattern 6 12) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 6 12) else d23 (change pattern 6 12)) = d881 pattern
  rw [s5249, s5178]
  rfl
theorem s5251 (pattern : Twelve) : d125 (change pattern 6 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d119 (change pattern 6 12)) = d125 pattern
  rw [s5169, s5238]
  rfl
theorem s5252 (pattern : Twelve) : d888 (change pattern 6 12) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 6 12) else d881 (change pattern 6 12)) = d888 pattern
  rw [s5251, s5250]
  rfl
theorem s5253 (pattern : Twelve) : d889 (change pattern 6 12) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 6 12) else d42 (change pattern 6 12)) = d889 pattern
  rw [s5169, s5170]
  rfl
theorem s5254 (pattern : Twelve) : d897 (change pattern 6 12) = d897 pattern := by
  change (if pattern.f then d889 (change pattern 6 12) else d888 (change pattern 6 12)) = d897 pattern
  rw [s5253, s5252]
  rfl
theorem s5255 (pattern : Twelve) : d901 (change pattern 6 12) = d901 pattern := by
  change (if pattern.e then d897 (change pattern 6 12) else d896 (change pattern 6 12)) = d901 pattern
  rw [s5254, s5248]
  rfl
theorem s5256 (pattern : Twelve) : d903 (change pattern 6 12) = d903 pattern := by
  change (if pattern.j then d901 (change pattern 6 12) else d900 (change pattern 6 12)) = d903 pattern
  rw [s5255, s5242]
  rfl
theorem s5257 (pattern : Twelve) : d904 (change pattern 6 12) = d904 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d899 (change pattern 6 12)) = d904 pattern
  rw [s5169, s5232]
  rfl
theorem s5258 (pattern : Twelve) : d905 (change pattern 6 12) = d905 pattern := by
  change (if pattern.d then d904 (change pattern 6 12) else d903 (change pattern 6 12)) = d905 pattern
  rw [s5257, s5256]
  rfl
theorem s5259 (pattern : Twelve) : d906 (change pattern 6 12) = d906 pattern := by
  change (if pattern.c then d905 (change pattern 6 12) else d902 (change pattern 6 12)) = d906 pattern
  rw [s5258, s5233]
  rfl
theorem s5260 (pattern : Twelve) : d1269 (change pattern 6 12) = d906 pattern := by
  change d906 (change pattern 6 12) = d906 pattern
  exact s5259 pattern
theorem s5261 (pattern : Twelve) : d1270 (change pattern 6 12) = d907 pattern := by
  change (if pattern.a then d1269 (change pattern 6 12) else d1268 (change pattern 6 12)) = d907 pattern
  rw [s5260, s5217]
  rfl
theorem s5262 (pattern : Twelve) : d1275 (change pattern 6 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 6 12) else d7 (change pattern 6 12)) = d1275 pattern
  rw [s5218, s5151]
  rfl
theorem s5263 (pattern : Twelve) : d1278 (change pattern 6 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 6 12) else d1275 (change pattern 6 12)) = d1278 pattern
  rw [s5219, s5262]
  rfl
theorem s5264 (pattern : Twelve) : d1284 (change pattern 6 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 6 12) else d1278 (change pattern 6 12)) = d1284 pattern
  rw [s5219, s5263]
  rfl
theorem s5265 (pattern : Twelve) : d1293 (change pattern 6 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 6 12) else d17 (change pattern 6 12)) = d1293 pattern
  rw [s5264, s5152]
  rfl
theorem s5266 (pattern : Twelve) : d1294 (change pattern 6 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d19 (change pattern 6 12)) = d1294 pattern
  rw [s5169, s5162]
  rfl
theorem s5267 (pattern : Twelve) : d1305 (change pattern 6 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 6 12) else d1293 (change pattern 6 12)) = d1305 pattern
  rw [s5266, s5265]
  rfl
theorem s5268 (pattern : Twelve) : d1276 (change pattern 6 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 6 12) else d9 (change pattern 6 12)) = d1276 pattern
  rw [s5237, s5177]
  rfl
theorem s5269 (pattern : Twelve) : d1279 (change pattern 6 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 6 12) else d1275 (change pattern 6 12)) = d1279 pattern
  rw [s5268, s5262]
  rfl
theorem s5270 (pattern : Twelve) : d1280 (change pattern 6 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d872 (change pattern 6 12)) = d1280 pattern
  rw [s5169, s5219]
  rfl
theorem s5271 (pattern : Twelve) : d1285 (change pattern 6 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 6 12) else d1279 (change pattern 6 12)) = d1285 pattern
  rw [s5270, s5269]
  rfl
theorem s5272 (pattern : Twelve) : d1295 (change pattern 6 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 6 12) else d827 (change pattern 6 12)) = d1295 pattern
  rw [s5271, s5184]
  rfl
theorem s5273 (pattern : Twelve) : d29 (change pattern 6 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d19 (change pattern 6 12)) = d29 pattern
  rw [s5169, s5162]
  rfl
theorem s5274 (pattern : Twelve) : d1286 (change pattern 6 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 6 12) else d817 (change pattern 6 12)) = d1286 pattern
  rw [s5273, s5168]
  rfl
theorem s5275 (pattern : Twelve) : d1296 (change pattern 6 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d1286 (change pattern 6 12)) = d1296 pattern
  rw [s5169, s5274]
  rfl
theorem s5276 (pattern : Twelve) : d1306 (change pattern 6 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 6 12) else d1295 (change pattern 6 12)) = d1306 pattern
  rw [s5275, s5272]
  rfl
theorem s5277 (pattern : Twelve) : d1313 (change pattern 6 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 6 12) else d1305 (change pattern 6 12)) = d1313 pattern
  rw [s5276, s5267]
  rfl
theorem s5278 (pattern : Twelve) : d1281 (change pattern 6 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 6 12) else d872 (change pattern 6 12)) = d1281 pattern
  rw [s5238, s5219]
  rfl
theorem s5279 (pattern : Twelve) : d1287 (change pattern 6 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 6 12) else d1279 (change pattern 6 12)) = d1287 pattern
  rw [s5278, s5269]
  rfl
theorem s5280 (pattern : Twelve) : d1297 (change pattern 6 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 6 12) else d34 (change pattern 6 12)) = d1297 pattern
  rw [s5279, s5179]
  rfl
theorem s5281 (pattern : Twelve) : d1298 (change pattern 6 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d817 (change pattern 6 12)) = d1298 pattern
  rw [s5169, s5168]
  rfl
theorem s5282 (pattern : Twelve) : d1307 (change pattern 6 12) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 6 12) else d1297 (change pattern 6 12)) = d1307 pattern
  rw [s5281, s5280]
  rfl
theorem s5283 (pattern : Twelve) : d1277 (change pattern 6 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 6 12) else d15 (change pattern 6 12)) = d1277 pattern
  rw [s5206, s5196]
  rfl
theorem s5284 (pattern : Twelve) : d1282 (change pattern 6 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 6 12) else d1276 (change pattern 6 12)) = d1282 pattern
  rw [s5283, s5268]
  rfl
theorem s5285 (pattern : Twelve) : d1288 (change pattern 6 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 6 12) else d1282 (change pattern 6 12)) = d1288 pattern
  rw [s5251, s5284]
  rfl
theorem s5286 (pattern : Twelve) : d1299 (change pattern 6 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 6 12) else d830 (change pattern 6 12)) = d1299 pattern
  rw [s5285, s5204]
  rfl
theorem s5287 (pattern : Twelve) : d1289 (change pattern 6 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 6 12) else d821 (change pattern 6 12)) = d1289 pattern
  rw [s5170, s5208]
  rfl
theorem s5288 (pattern : Twelve) : d1300 (change pattern 6 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d1289 (change pattern 6 12)) = d1300 pattern
  rw [s5169, s5287]
  rfl
theorem s5289 (pattern : Twelve) : d1308 (change pattern 6 12) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 6 12) else d1299 (change pattern 6 12)) = d1308 pattern
  rw [s5288, s5286]
  rfl
theorem s5290 (pattern : Twelve) : d1314 (change pattern 6 12) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 6 12) else d1307 (change pattern 6 12)) = d1314 pattern
  rw [s5289, s5282]
  rfl
theorem s5291 (pattern : Twelve) : d1315 (change pattern 6 12) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d1306 (change pattern 6 12)) = d1315 pattern
  rw [s5169, s5276]
  rfl
theorem s5292 (pattern : Twelve) : d1319 (change pattern 6 12) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 6 12) else d1314 (change pattern 6 12)) = d1319 pattern
  rw [s5291, s5290]
  rfl
theorem s5293 (pattern : Twelve) : d1321 (change pattern 6 12) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 6 12) else d1313 (change pattern 6 12)) = d1321 pattern
  rw [s5292, s5277]
  rfl
theorem s5294 (pattern : Twelve) : d1637 (change pattern 6 12) = d1321 pattern := by
  change d1321 (change pattern 6 12) = d1321 pattern
  exact s5293 pattern
theorem s5295 (pattern : Twelve) : d1324 (change pattern 6 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 6 12) else d11 (change pattern 6 12)) = d1324 pattern
  rw [s5164, s5161]
  rfl
theorem s5296 (pattern : Twelve) : d1325 (change pattern 6 12) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 6 12) else d1275 (change pattern 6 12)) = d1325 pattern
  rw [s5295, s5262]
  rfl
theorem s5297 (pattern : Twelve) : d1326 (change pattern 6 12) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 6 12) else d872 (change pattern 6 12)) = d1326 pattern
  rw [s5295, s5219]
  rfl
theorem s5298 (pattern : Twelve) : d1333 (change pattern 6 12) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 6 12) else d1325 (change pattern 6 12)) = d1333 pattern
  rw [s5297, s5296]
  rfl
theorem s5299 (pattern : Twelve) : d1339 (change pattern 6 12) = d1339 pattern := by
  change (if pattern.f then d1333 (change pattern 6 12) else d17 (change pattern 6 12)) = d1339 pattern
  rw [s5298, s5152]
  rfl
theorem s5300 (pattern : Twelve) : d1345 (change pattern 6 12) = d1345 pattern := by
  change (if pattern.e then d1294 (change pattern 6 12) else d1339 (change pattern 6 12)) = d1345 pattern
  rw [s5266, s5299]
  rfl
theorem s5301 (pattern : Twelve) : d1327 (change pattern 6 12) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 6 12) else d1275 (change pattern 6 12)) = d1327 pattern
  rw [s5238, s5262]
  rfl
theorem s5302 (pattern : Twelve) : d1334 (change pattern 6 12) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 6 12) else d1327 (change pattern 6 12)) = d1334 pattern
  rw [s5270, s5301]
  rfl
theorem s5303 (pattern : Twelve) : d1340 (change pattern 6 12) = d1340 pattern := by
  change (if pattern.f then d1334 (change pattern 6 12) else d827 (change pattern 6 12)) = d1340 pattern
  rw [s5302, s5184]
  rfl
theorem s5304 (pattern : Twelve) : d1346 (change pattern 6 12) = d1346 pattern := by
  change (if pattern.e then d1296 (change pattern 6 12) else d1340 (change pattern 6 12)) = d1346 pattern
  rw [s5275, s5303]
  rfl
theorem s5305 (pattern : Twelve) : d1349 (change pattern 6 12) = d1349 pattern := by
  change (if pattern.j then d1346 (change pattern 6 12) else d1345 (change pattern 6 12)) = d1349 pattern
  rw [s5304, s5300]
  rfl
theorem s5306 (pattern : Twelve) : d1328 (change pattern 6 12) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 6 12) else d872 (change pattern 6 12)) = d1328 pattern
  rw [s5283, s5219]
  rfl
theorem s5307 (pattern : Twelve) : d1335 (change pattern 6 12) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 6 12) else d1327 (change pattern 6 12)) = d1335 pattern
  rw [s5306, s5301]
  rfl
theorem s5308 (pattern : Twelve) : d1341 (change pattern 6 12) = d1341 pattern := by
  change (if pattern.f then d1335 (change pattern 6 12) else d34 (change pattern 6 12)) = d1341 pattern
  rw [s5307, s5179]
  rfl
theorem s5309 (pattern : Twelve) : d20 (change pattern 6 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 6 12) else d12 (change pattern 6 12)) = d20 pattern
  rw [s5205, s5166]
  rfl
theorem s5310 (pattern : Twelve) : d1329 (change pattern 6 12) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 6 12) else d19 (change pattern 6 12)) = d1329 pattern
  rw [s5309, s5162]
  rfl
theorem s5311 (pattern : Twelve) : d1336 (change pattern 6 12) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 6 12) else d817 (change pattern 6 12)) = d1336 pattern
  rw [s5310, s5168]
  rfl
theorem s5312 (pattern : Twelve) : d1342 (change pattern 6 12) = d1342 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d1336 (change pattern 6 12)) = d1342 pattern
  rw [s5169, s5311]
  rfl
theorem s5313 (pattern : Twelve) : d1347 (change pattern 6 12) = d1347 pattern := by
  change (if pattern.e then d1342 (change pattern 6 12) else d1341 (change pattern 6 12)) = d1347 pattern
  rw [s5312, s5308]
  rfl
theorem s5314 (pattern : Twelve) : d1330 (change pattern 6 12) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d1276 (change pattern 6 12)) = d1330 pattern
  rw [s5169, s5268]
  rfl
theorem s5315 (pattern : Twelve) : d1331 (change pattern 6 12) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d1277 (change pattern 6 12)) = d1331 pattern
  rw [s5169, s5283]
  rfl
theorem s5316 (pattern : Twelve) : d1337 (change pattern 6 12) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 6 12) else d1330 (change pattern 6 12)) = d1337 pattern
  rw [s5315, s5314]
  rfl
theorem s5317 (pattern : Twelve) : d1343 (change pattern 6 12) = d1343 pattern := by
  change (if pattern.f then d1337 (change pattern 6 12) else d830 (change pattern 6 12)) = d1343 pattern
  rw [s5316, s5204]
  rfl
theorem s5318 (pattern : Twelve) : d1332 (change pattern 6 12) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 6 12) else d25 (change pattern 6 12)) = d1332 pattern
  rw [s5243, s5167]
  rfl
theorem s5319 (pattern : Twelve) : d128 (change pattern 6 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d20 (change pattern 6 12)) = d128 pattern
  rw [s5169, s5309]
  rfl
theorem s5320 (pattern : Twelve) : d1338 (change pattern 6 12) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 6 12) else d1332 (change pattern 6 12)) = d1338 pattern
  rw [s5319, s5318]
  rfl
theorem s5321 (pattern : Twelve) : d1344 (change pattern 6 12) = d1344 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d1338 (change pattern 6 12)) = d1344 pattern
  rw [s5169, s5320]
  rfl
theorem s5322 (pattern : Twelve) : d1348 (change pattern 6 12) = d1348 pattern := by
  change (if pattern.e then d1344 (change pattern 6 12) else d1343 (change pattern 6 12)) = d1348 pattern
  rw [s5321, s5317]
  rfl
theorem s5323 (pattern : Twelve) : d1350 (change pattern 6 12) = d1350 pattern := by
  change (if pattern.j then d1348 (change pattern 6 12) else d1347 (change pattern 6 12)) = d1350 pattern
  rw [s5322, s5313]
  rfl
theorem s5324 (pattern : Twelve) : d1351 (change pattern 6 12) = d1351 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d1346 (change pattern 6 12)) = d1351 pattern
  rw [s5169, s5304]
  rfl
theorem s5325 (pattern : Twelve) : d1352 (change pattern 6 12) = d1352 pattern := by
  change (if pattern.d then d1351 (change pattern 6 12) else d1350 (change pattern 6 12)) = d1352 pattern
  rw [s5324, s5323]
  rfl
theorem s5326 (pattern : Twelve) : d1353 (change pattern 6 12) = d1353 pattern := by
  change (if pattern.c then d1352 (change pattern 6 12) else d1349 (change pattern 6 12)) = d1353 pattern
  rw [s5325, s5305]
  rfl
theorem s5327 (pattern : Twelve) : d1638 (change pattern 6 12) = d1353 pattern := by
  change d1353 (change pattern 6 12) = d1353 pattern
  exact s5326 pattern
theorem s5328 (pattern : Twelve) : d1639 (change pattern 6 12) = d1354 pattern := by
  change (if pattern.a then d1638 (change pattern 6 12) else d1637 (change pattern 6 12)) = d1354 pattern
  rw [s5327, s5294]
  rfl
theorem s5329 (pattern : Twelve) : d1649 (change pattern 6 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 6 12) else d19 (change pattern 6 12)) = d1649 pattern
  rw [s5295, s5162]
  rfl
theorem s5330 (pattern : Twelve) : d1650 (change pattern 6 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d25 (change pattern 6 12)) = d1650 pattern
  rw [s5169, s5167]
  rfl
theorem s5331 (pattern : Twelve) : d1656 (change pattern 6 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 6 12) else d1649 (change pattern 6 12)) = d1656 pattern
  rw [s5330, s5329]
  rfl
theorem s5332 (pattern : Twelve) : d1644 (change pattern 6 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 6 12) else d1324 (change pattern 6 12)) = d1644 pattern
  rw [s5309, s5295]
  rfl
theorem s5333 (pattern : Twelve) : d1645 (change pattern 6 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d1324 (change pattern 6 12)) = d1645 pattern
  rw [s5169, s5295]
  rfl
theorem s5334 (pattern : Twelve) : d1647 (change pattern 6 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 6 12) else d1644 (change pattern 6 12)) = d1647 pattern
  rw [s5333, s5332]
  rfl
theorem s5335 (pattern : Twelve) : d1651 (change pattern 6 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 6 12) else d1286 (change pattern 6 12)) = d1651 pattern
  rw [s5334, s5274]
  rfl
theorem s5336 (pattern : Twelve) : d1657 (change pattern 6 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 6 12) else d1651 (change pattern 6 12)) = d1657 pattern
  rw [s5288, s5335]
  rfl
theorem s5337 (pattern : Twelve) : d1660 (change pattern 6 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 6 12) else d1656 (change pattern 6 12)) = d1660 pattern
  rw [s5336, s5331]
  rfl
theorem s5338 (pattern : Twelve) : d1652 (change pattern 6 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 6 12) else d817 (change pattern 6 12)) = d1652 pattern
  rw [s5332, s5168]
  rfl
theorem s5339 (pattern : Twelve) : d1653 (change pattern 6 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d821 (change pattern 6 12)) = d1653 pattern
  rw [s5169, s5208]
  rfl
theorem s5340 (pattern : Twelve) : d1658 (change pattern 6 12) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 6 12) else d1652 (change pattern 6 12)) = d1658 pattern
  rw [s5339, s5338]
  rfl
theorem s5341 (pattern : Twelve) : d1646 (change pattern 6 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 6 12) else d20 (change pattern 6 12)) = d1646 pattern
  rw [s5243, s5309]
  rfl
theorem s5342 (pattern : Twelve) : d1648 (change pattern 6 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 6 12) else d1646 (change pattern 6 12)) = d1648 pattern
  rw [s5319, s5341]
  rfl
theorem s5343 (pattern : Twelve) : d1654 (change pattern 6 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 6 12) else d1289 (change pattern 6 12)) = d1654 pattern
  rw [s5342, s5287]
  rfl
theorem s5344 (pattern : Twelve) : d1655 (change pattern 6 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d822 (change pattern 6 12)) = d1655 pattern
  rw [s5169, s5209]
  rfl
theorem s5345 (pattern : Twelve) : d1659 (change pattern 6 12) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 6 12) else d1654 (change pattern 6 12)) = d1659 pattern
  rw [s5344, s5343]
  rfl
theorem s5346 (pattern : Twelve) : d1661 (change pattern 6 12) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 6 12) else d1658 (change pattern 6 12)) = d1661 pattern
  rw [s5345, s5340]
  rfl
theorem s5347 (pattern : Twelve) : d1662 (change pattern 6 12) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d1657 (change pattern 6 12)) = d1662 pattern
  rw [s5169, s5336]
  rfl
theorem s5348 (pattern : Twelve) : d1663 (change pattern 6 12) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 6 12) else d1661 (change pattern 6 12)) = d1663 pattern
  rw [s5347, s5346]
  rfl
theorem s5349 (pattern : Twelve) : d1664 (change pattern 6 12) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 6 12) else d1660 (change pattern 6 12)) = d1664 pattern
  rw [s5348, s5337]
  rfl
theorem s5350 (pattern : Twelve) : d1828 (change pattern 6 12) = d1664 pattern := by
  change d1664 (change pattern 6 12) = d1664 pattern
  exact s5349 pattern
theorem s5351 (pattern : Twelve) : d1668 (change pattern 6 12) = d1668 pattern := by
  change (if pattern.f then d1644 (change pattern 6 12) else d19 (change pattern 6 12)) = d1668 pattern
  rw [s5332, s5162]
  rfl
theorem s5352 (pattern : Twelve) : d1671 (change pattern 6 12) = d1671 pattern := by
  change (if pattern.e then d1650 (change pattern 6 12) else d1668 (change pattern 6 12)) = d1671 pattern
  rw [s5330, s5351]
  rfl
theorem s5353 (pattern : Twelve) : d1674 (change pattern 6 12) = d1674 pattern := by
  change (if pattern.j then d1657 (change pattern 6 12) else d1671 (change pattern 6 12)) = d1674 pattern
  rw [s5336, s5352]
  rfl
theorem s5354 (pattern : Twelve) : d1665 (change pattern 6 12) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 6 12) else d1324 (change pattern 6 12)) = d1665 pattern
  rw [s5243, s5295]
  rfl
theorem s5355 (pattern : Twelve) : d1666 (change pattern 6 12) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 6 12) else d1644 (change pattern 6 12)) = d1666 pattern
  rw [s5354, s5332]
  rfl
theorem s5356 (pattern : Twelve) : d1669 (change pattern 6 12) = d1669 pattern := by
  change (if pattern.f then d1666 (change pattern 6 12) else d817 (change pattern 6 12)) = d1669 pattern
  rw [s5355, s5168]
  rfl
theorem s5357 (pattern : Twelve) : d1672 (change pattern 6 12) = d1672 pattern := by
  change (if pattern.e then d1300 (change pattern 6 12) else d1669 (change pattern 6 12)) = d1672 pattern
  rw [s5288, s5356]
  rfl
theorem s5358 (pattern : Twelve) : d183 (change pattern 6 12) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d22 (change pattern 6 12)) = d183 pattern
  rw [s5169, s5243]
  rfl
theorem s5359 (pattern : Twelve) : d1667 (change pattern 6 12) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 6 12) else d128 (change pattern 6 12)) = d1667 pattern
  rw [s5358, s5319]
  rfl
theorem s5360 (pattern : Twelve) : d1670 (change pattern 6 12) = d1670 pattern := by
  change (if pattern.f then d1667 (change pattern 6 12) else d1289 (change pattern 6 12)) = d1670 pattern
  rw [s5359, s5287]
  rfl
theorem s5361 (pattern : Twelve) : d1252 (change pattern 6 12) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 6 12) else d822 (change pattern 6 12)) = d1252 pattern
  rw [s5169, s5209]
  rfl
theorem s5362 (pattern : Twelve) : d1626 (change pattern 6 12) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 6 12) else d1252 (change pattern 6 12)) = d1626 pattern
  rw [s5169, s5361]
  rfl
theorem s5363 (pattern : Twelve) : d1673 (change pattern 6 12) = d1673 pattern := by
  change (if pattern.e then d1626 (change pattern 6 12) else d1670 (change pattern 6 12)) = d1673 pattern
  rw [s5362, s5360]
  rfl
theorem s5364 (pattern : Twelve) : d1675 (change pattern 6 12) = d1675 pattern := by
  change (if pattern.j then d1673 (change pattern 6 12) else d1672 (change pattern 6 12)) = d1675 pattern
  rw [s5363, s5357]
  rfl
theorem s5365 (pattern : Twelve) : d1676 (change pattern 6 12) = d1676 pattern := by
  change (if pattern.d then d1662 (change pattern 6 12) else d1675 (change pattern 6 12)) = d1676 pattern
  rw [s5347, s5364]
  rfl
theorem s5366 (pattern : Twelve) : d1677 (change pattern 6 12) = d1677 pattern := by
  change (if pattern.c then d1676 (change pattern 6 12) else d1674 (change pattern 6 12)) = d1677 pattern
  rw [s5365, s5353]
  rfl
theorem s5367 (pattern : Twelve) : d1829 (change pattern 6 12) = d1677 pattern := by
  change d1677 (change pattern 6 12) = d1677 pattern
  exact s5366 pattern
theorem s5368 (pattern : Twelve) : d1830 (change pattern 6 12) = d1678 pattern := by
  change (if pattern.a then d1829 (change pattern 6 12) else d1828 (change pattern 6 12)) = d1678 pattern
  rw [s5367, s5350]
  rfl
theorem s5369 (pattern : Twelve) : d26 (change pattern 6 12) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 6 12) else d0 (change pattern 6 12)) = d26 pattern
  rw [s5150, s5149]
  rfl
theorem s5370 (pattern : Twelve) : d50 (change pattern 6 12) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 6 12) else d26 (change pattern 6 12)) = d50 pattern
  rw [s5153, s5369]
  rfl
theorem s5371 (pattern : Twelve) : d72 (change pattern 6 12) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 6 12) else d0 (change pattern 6 12)) = d72 pattern
  rw [s5370, s5149]
  rfl
theorem s5372 (pattern : Twelve) : d18 (change pattern 6 12) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 6 12) else d8 (change pattern 6 12)) = d18 pattern
  rw [s5177, s5218]
  rfl
theorem s5373 (pattern : Twelve) : d28 (change pattern 6 12) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 6 12) else d17 (change pattern 6 12)) = d28 pattern
  rw [s5372, s5152]
  rfl
theorem s5374 (pattern : Twelve) : d51 (change pattern 6 12) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 6 12) else d28 (change pattern 6 12)) = d51 pattern
  rw [s5273, s5373]
  rfl
theorem s5375 (pattern : Twelve) : d73 (change pattern 6 12) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 6 12) else d0 (change pattern 6 12)) = d73 pattern
  rw [s5374, s5149]
  rfl
theorem s5376 (pattern : Twelve) : d91 (change pattern 6 12) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 6 12) else d72 (change pattern 6 12)) = d91 pattern
  rw [s5375, s5371]
  rfl
theorem s5377 (pattern : Twelve) : d31 (change pattern 6 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 6 12) else d0 (change pattern 6 12)) = d31 pattern
  rw [s5309, s5149]
  rfl
theorem s5378 (pattern : Twelve) : d52 (change pattern 6 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 6 12) else d30 (change pattern 6 12)) = d52 pattern
  rw [s5377, s5174]
  rfl
theorem s5379 (pattern : Twelve) : d32 (change pattern 6 12) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 6 12) else d17 (change pattern 6 12)) = d32 pattern
  rw [s5207, s5152]
  rfl
theorem s5380 (pattern : Twelve) : d53 (change pattern 6 12) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 6 12) else d30 (change pattern 6 12)) = d53 pattern
  rw [s5379, s5174]
  rfl
theorem s5381 (pattern : Twelve) : d74 (change pattern 6 12) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 6 12) else d52 (change pattern 6 12)) = d74 pattern
  rw [s5380, s5378]
  rfl
theorem s5382 (pattern : Twelve) : d33 (change pattern 6 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 6 12) else d0 (change pattern 6 12)) = d33 pattern
  rw [s5243, s5149]
  rfl
theorem s5383 (pattern : Twelve) : d54 (change pattern 6 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 6 12) else d30 (change pattern 6 12)) = d54 pattern
  rw [s5382, s5174]
  rfl
theorem s5384 (pattern : Twelve) : d55 (change pattern 6 12) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 6 12) else d34 (change pattern 6 12)) = d55 pattern
  rw [s5273, s5179]
  rfl
theorem s5385 (pattern : Twelve) : d75 (change pattern 6 12) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 6 12) else d54 (change pattern 6 12)) = d75 pattern
  rw [s5384, s5383]
  rfl
theorem s5386 (pattern : Twelve) : d92 (change pattern 6 12) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 6 12) else d74 (change pattern 6 12)) = d92 pattern
  rw [s5385, s5381]
  rfl
theorem s5387 (pattern : Twelve) : d102 (change pattern 6 12) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 6 12) else d91 (change pattern 6 12)) = d102 pattern
  rw [s5386, s5376]
  rfl
theorem s5388 (pattern : Twelve) : d76 (change pattern 6 12) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 6 12) else d0 (change pattern 6 12)) = d76 pattern
  rw [s5384, s5149]
  rfl
theorem s5389 (pattern : Twelve) : d93 (change pattern 6 12) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 6 12) else d72 (change pattern 6 12)) = d93 pattern
  rw [s5388, s5371]
  rfl
theorem s5390 (pattern : Twelve) : d57 (change pattern 6 12) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 6 12) else d30 (change pattern 6 12)) = d57 pattern
  rw [s5183, s5174]
  rfl
theorem s5391 (pattern : Twelve) : d77 (change pattern 6 12) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 6 12) else d56 (change pattern 6 12)) = d77 pattern
  rw [s5390, s5176]
  rfl
theorem s5392 (pattern : Twelve) : d78 (change pattern 6 12) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 6 12) else d56 (change pattern 6 12)) = d78 pattern
  rw [s5384, s5176]
  rfl
theorem s5393 (pattern : Twelve) : d94 (change pattern 6 12) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 6 12) else d77 (change pattern 6 12)) = d94 pattern
  rw [s5392, s5391]
  rfl
theorem s5394 (pattern : Twelve) : d103 (change pattern 6 12) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 6 12) else d93 (change pattern 6 12)) = d103 pattern
  rw [s5393, s5389]
  rfl
theorem s5395 (pattern : Twelve) : d110 (change pattern 6 12) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 6 12) else d102 (change pattern 6 12)) = d110 pattern
  rw [s5394, s5387]
  rfl
theorem s5396 (pattern : Twelve) : d37 (change pattern 6 12) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 6 12) else d17 (change pattern 6 12)) = d37 pattern
  rw [s5160, s5152]
  rfl
theorem s5397 (pattern : Twelve) : d58 (change pattern 6 12) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 6 12) else d30 (change pattern 6 12)) = d58 pattern
  rw [s5396, s5174]
  rfl
theorem s5398 (pattern : Twelve) : d79 (change pattern 6 12) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 6 12) else d30 (change pattern 6 12)) = d79 pattern
  rw [s5397, s5174]
  rfl
theorem s5399 (pattern : Twelve) : d80 (change pattern 6 12) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 6 12) else d30 (change pattern 6 12)) = d80 pattern
  rw [s5384, s5174]
  rfl
end NetHack.Sokoban21.Diagram
