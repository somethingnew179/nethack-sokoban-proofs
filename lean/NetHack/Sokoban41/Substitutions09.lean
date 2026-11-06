/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions08
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s1350 (pattern : Ten) : d205 (change pattern 6 10) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 6 10) else d200 (change pattern 6 10)) = d205 pattern
  rw [s1278, s1349]
  rfl
theorem s1351 (pattern : Ten) : d209 (change pattern 6 10) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 6 10) else d205 (change pattern 6 10)) = d209 pattern
  rw [s1278, s1350]
  rfl
theorem s1352 (pattern : Ten) : d210 (change pattern 6 10) = d210 pattern := by
  change (if pattern.h then d10 (change pattern 6 10) else d206 (change pattern 6 10)) = d210 pattern
  rw [s1278, s1345]
  rfl
theorem s1353 (pattern : Ten) : d328 (change pattern 6 10) = d328 pattern := by
  change (if pattern.c then d10 (change pattern 6 10) else d210 (change pattern 6 10)) = d328 pattern
  rw [s1278, s1352]
  rfl
theorem s1354 (pattern : Ten) : d330 (change pattern 6 10) = d330 pattern := by
  change (if pattern.e then d328 (change pattern 6 10) else d209 (change pattern 6 10)) = d330 pattern
  rw [s1353, s1351]
  rfl
theorem s1355 (pattern : Ten) : d331 (change pattern 6 10) = d575 pattern := by
  change (if pattern.d then d330 (change pattern 6 10) else d329 (change pattern 6 10)) = d575 pattern
  rw [s1354, s1348]
  rfl
theorem s1356 (pattern : Ten) : d2 (change pattern 10 6) = d2 pattern := by
  rfl
theorem s1357 (pattern : Ten) : d4 (change pattern 10 6) = d4 pattern := by
  rfl
theorem s1358 (pattern : Ten) : d44 (change pattern 10 6) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 10 6) else d2 (change pattern 10 6)) = d44 pattern
  rw [s1357, s1356]
  rfl
theorem s1359 (pattern : Ten) : d6 (change pattern 10 6) = d6 pattern := by
  rfl
theorem s1360 (pattern : Ten) : d10 (change pattern 10 6) = d10 pattern := by
  rfl
theorem s1361 (pattern : Ten) : d43 (change pattern 10 6) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 10 6) else d6 (change pattern 10 6)) = d43 pattern
  rw [s1360, s1359]
  rfl
theorem s1362 (pattern : Ten) : d50 (change pattern 10 6) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 10 6) else d44 (change pattern 10 6)) = d50 pattern
  rw [s1361, s1358]
  rfl
theorem s1363 (pattern : Ten) : d8 (change pattern 10 6) = d8 pattern := by
  rfl
theorem s1364 (pattern : Ten) : d45 (change pattern 10 6) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 10 6) else d8 (change pattern 10 6)) = d45 pattern
  rw [s1360, s1363]
  rfl
theorem s1365 (pattern : Ten) : d51 (change pattern 10 6) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 10 6) else d45 (change pattern 10 6)) = d51 pattern
  rw [s1360, s1364]
  rfl
theorem s1366 (pattern : Ten) : d55 (change pattern 10 6) = d55 pattern := by
  change (if pattern.h then d51 (change pattern 10 6) else d50 (change pattern 10 6)) = d55 pattern
  rw [s1365, s1362]
  rfl
theorem s1367 (pattern : Ten) : d160 (change pattern 10 6) = d55 pattern := by
  change d55 (change pattern 10 6) = d55 pattern
  exact s1366 pattern
theorem s1368 (pattern : Ten) : d157 (change pattern 10 6) = d157 pattern := by
  change (if pattern.j then d6 (change pattern 10 6) else d4 (change pattern 10 6)) = d157 pattern
  rw [s1359, s1357]
  rfl
theorem s1369 (pattern : Ten) : d158 (change pattern 10 6) = d158 pattern := by
  change (if pattern.i then d45 (change pattern 10 6) else d157 (change pattern 10 6)) = d158 pattern
  rw [s1364, s1368]
  rfl
theorem s1370 (pattern : Ten) : d159 (change pattern 10 6) = d159 pattern := by
  change (if pattern.h then d10 (change pattern 10 6) else d158 (change pattern 10 6)) = d159 pattern
  rw [s1360, s1369]
  rfl
theorem s1371 (pattern : Ten) : d161 (change pattern 10 6) = d159 pattern := by
  change d159 (change pattern 10 6) = d159 pattern
  exact s1370 pattern
theorem s1372 (pattern : Ten) : d165 (change pattern 10 6) = d576 pattern := by
  change (if pattern.c then d161 (change pattern 10 6) else d160 (change pattern 10 6)) = d576 pattern
  rw [s1371, s1367]
  rfl
theorem s1373 (pattern : Ten) : d162 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1374 (pattern : Ten) : d163 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1375 (pattern : Ten) : d166 (change pattern 10 6) = d10 pattern := by
  change (if pattern.c then d163 (change pattern 10 6) else d162 (change pattern 10 6)) = d10 pattern
  rw [s1374, s1373]
  simp only [ite_self]
theorem s1376 (pattern : Ten) : d168 (change pattern 10 6) = d577 pattern := by
  change (if pattern.e then d166 (change pattern 10 6) else d165 (change pattern 10 6)) = d577 pattern
  rw [s1375, s1372]
  rfl
theorem s1377 (pattern : Ten) : d9 (change pattern 10 6) = d9 pattern := by
  rfl
theorem s1378 (pattern : Ten) : d39 (change pattern 10 6) = d39 pattern := by
  change (if pattern.b then d10 (change pattern 10 6) else d9 (change pattern 10 6)) = d39 pattern
  rw [s1360, s1377]
  rfl
theorem s1379 (pattern : Ten) : d41 (change pattern 10 6) = d41 pattern := by
  change (if pattern.a then d10 (change pattern 10 6) else d39 (change pattern 10 6)) = d41 pattern
  rw [s1360, s1378]
  rfl
theorem s1380 (pattern : Ten) : d47 (change pattern 10 6) = d47 pattern := by
  change (if pattern.j then d10 (change pattern 10 6) else d41 (change pattern 10 6)) = d47 pattern
  rw [s1360, s1379]
  rfl
theorem s1381 (pattern : Ten) : d53 (change pattern 10 6) = d53 pattern := by
  change (if pattern.i then d10 (change pattern 10 6) else d47 (change pattern 10 6)) = d53 pattern
  rw [s1360, s1380]
  rfl
theorem s1382 (pattern : Ten) : d57 (change pattern 10 6) = d57 pattern := by
  change (if pattern.h then d10 (change pattern 10 6) else d53 (change pattern 10 6)) = d57 pattern
  rw [s1360, s1381]
  rfl
theorem s1383 (pattern : Ten) : d164 (change pattern 10 6) = d57 pattern := by
  change d57 (change pattern 10 6) = d57 pattern
  exact s1382 pattern
theorem s1384 (pattern : Ten) : d60 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1385 (pattern : Ten) : d167 (change pattern 10 6) = d578 pattern := by
  change (if pattern.c then d60 (change pattern 10 6) else d164 (change pattern 10 6)) = d578 pattern
  rw [s1384, s1383]
  rfl
theorem s1386 (pattern : Ten) : d61 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1387 (pattern : Ten) : d63 (change pattern 10 6) = d10 pattern := by
  change (if pattern.c then d61 (change pattern 10 6) else d60 (change pattern 10 6)) = d10 pattern
  rw [s1386, s1384]
  simp only [ite_self]
theorem s1388 (pattern : Ten) : d169 (change pattern 10 6) = d579 pattern := by
  change (if pattern.e then d63 (change pattern 10 6) else d167 (change pattern 10 6)) = d579 pattern
  rw [s1387, s1385]
  rfl
theorem s1389 (pattern : Ten) : d170 (change pattern 10 6) = d580 pattern := by
  change (if pattern.d then d169 (change pattern 10 6) else d168 (change pattern 10 6)) = d580 pattern
  rw [s1388, s1376]
  rfl
theorem s1390 (pattern : Ten) : d3 (change pattern 10 6) = d3 pattern := by
  rfl
theorem s1391 (pattern : Ten) : d172 (change pattern 10 6) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 10 6) else d2 (change pattern 10 6)) = d172 pattern
  rw [s1390, s1356]
  rfl
theorem s1392 (pattern : Ten) : d310 (change pattern 10 6) = d310 pattern := by
  change (if pattern.a then d4 (change pattern 10 6) else d3 (change pattern 10 6)) = d310 pattern
  rw [s1357, s1390]
  rfl
theorem s1393 (pattern : Ten) : d314 (change pattern 10 6) = d314 pattern := by
  change (if pattern.f then d310 (change pattern 10 6) else d172 (change pattern 10 6)) = d314 pattern
  rw [s1392, s1391]
  rfl
theorem s1394 (pattern : Ten) : d5 (change pattern 10 6) = d5 pattern := by
  rfl
theorem s1395 (pattern : Ten) : d193 (change pattern 10 6) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 10 6) else d4 (change pattern 10 6)) = d193 pattern
  rw [s1394, s1357]
  rfl
theorem s1396 (pattern : Ten) : d311 (change pattern 10 6) = d311 pattern := by
  change (if pattern.a then d6 (change pattern 10 6) else d5 (change pattern 10 6)) = d311 pattern
  rw [s1359, s1394]
  rfl
theorem s1397 (pattern : Ten) : d315 (change pattern 10 6) = d315 pattern := by
  change (if pattern.f then d311 (change pattern 10 6) else d193 (change pattern 10 6)) = d315 pattern
  rw [s1396, s1395]
  rfl
theorem s1398 (pattern : Ten) : d320 (change pattern 10 6) = d320 pattern := by
  change (if pattern.j then d315 (change pattern 10 6) else d314 (change pattern 10 6)) = d320 pattern
  rw [s1397, s1393]
  rfl
theorem s1399 (pattern : Ten) : d7 (change pattern 10 6) = d7 pattern := by
  rfl
theorem s1400 (pattern : Ten) : d194 (change pattern 10 6) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 10 6) else d6 (change pattern 10 6)) = d194 pattern
  rw [s1399, s1359]
  rfl
theorem s1401 (pattern : Ten) : d312 (change pattern 10 6) = d312 pattern := by
  change (if pattern.a then d8 (change pattern 10 6) else d7 (change pattern 10 6)) = d312 pattern
  rw [s1363, s1399]
  rfl
theorem s1402 (pattern : Ten) : d316 (change pattern 10 6) = d316 pattern := by
  change (if pattern.f then d312 (change pattern 10 6) else d194 (change pattern 10 6)) = d316 pattern
  rw [s1401, s1400]
  rfl
theorem s1403 (pattern : Ten) : d319 (change pattern 10 6) = d319 pattern := by
  change (if pattern.j then d10 (change pattern 10 6) else d316 (change pattern 10 6)) = d319 pattern
  rw [s1360, s1402]
  rfl
theorem s1404 (pattern : Ten) : d323 (change pattern 10 6) = d323 pattern := by
  change (if pattern.i then d319 (change pattern 10 6) else d320 (change pattern 10 6)) = d323 pattern
  rw [s1403, s1398]
  rfl
theorem s1405 (pattern : Ten) : d195 (change pattern 10 6) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 10 6) else d8 (change pattern 10 6)) = d195 pattern
  rw [s1377, s1363]
  rfl
theorem s1406 (pattern : Ten) : d11 (change pattern 10 6) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 6) else d9 (change pattern 10 6)) = d11 pattern
  rw [s1360, s1377]
  rfl
theorem s1407 (pattern : Ten) : d196 (change pattern 10 6) = d196 pattern := by
  change (if pattern.f then d11 (change pattern 10 6) else d195 (change pattern 10 6)) = d196 pattern
  rw [s1406, s1405]
  rfl
theorem s1408 (pattern : Ten) : d201 (change pattern 10 6) = d201 pattern := by
  change (if pattern.j then d10 (change pattern 10 6) else d196 (change pattern 10 6)) = d201 pattern
  rw [s1360, s1407]
  rfl
theorem s1409 (pattern : Ten) : d206 (change pattern 10 6) = d206 pattern := by
  change (if pattern.i then d10 (change pattern 10 6) else d201 (change pattern 10 6)) = d206 pattern
  rw [s1360, s1408]
  rfl
theorem s1410 (pattern : Ten) : d325 (change pattern 10 6) = d325 pattern := by
  change (if pattern.h then d206 (change pattern 10 6) else d323 (change pattern 10 6)) = d325 pattern
  rw [s1409, s1404]
  rfl
theorem s1411 (pattern : Ten) : d344 (change pattern 10 6) = d325 pattern := by
  change d325 (change pattern 10 6) = d325 pattern
  exact s1410 pattern
theorem s1412 (pattern : Ten) : d341 (change pattern 10 6) = d341 pattern := by
  change (if pattern.j then d316 (change pattern 10 6) else d315 (change pattern 10 6)) = d341 pattern
  rw [s1402, s1397]
  rfl
theorem s1413 (pattern : Ten) : d342 (change pattern 10 6) = d342 pattern := by
  change (if pattern.i then d201 (change pattern 10 6) else d341 (change pattern 10 6)) = d342 pattern
  rw [s1408, s1412]
  rfl
theorem s1414 (pattern : Ten) : d343 (change pattern 10 6) = d343 pattern := by
  change (if pattern.h then d10 (change pattern 10 6) else d342 (change pattern 10 6)) = d343 pattern
  rw [s1360, s1413]
  rfl
theorem s1415 (pattern : Ten) : d345 (change pattern 10 6) = d343 pattern := by
  change d343 (change pattern 10 6) = d343 pattern
  exact s1414 pattern
theorem s1416 (pattern : Ten) : d346 (change pattern 10 6) = d581 pattern := by
  change (if pattern.c then d345 (change pattern 10 6) else d344 (change pattern 10 6)) = d581 pattern
  rw [s1415, s1411]
  rfl
theorem s1417 (pattern : Ten) : d333 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1418 (pattern : Ten) : d334 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1419 (pattern : Ten) : d336 (change pattern 10 6) = d10 pattern := by
  change (if pattern.c then d334 (change pattern 10 6) else d333 (change pattern 10 6)) = d10 pattern
  rw [s1418, s1417]
  simp only [ite_self]
theorem s1420 (pattern : Ten) : d347 (change pattern 10 6) = d582 pattern := by
  change (if pattern.e then d336 (change pattern 10 6) else d346 (change pattern 10 6)) = d582 pattern
  rw [s1419, s1416]
  rfl
theorem s1421 (pattern : Ten) : d214 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1422 (pattern : Ten) : d335 (change pattern 10 6) = d10 pattern := by
  change d10 (change pattern 10 6) = d10 pattern
  exact s1360 pattern
theorem s1423 (pattern : Ten) : d337 (change pattern 10 6) = d10 pattern := by
  change (if pattern.c then d10 (change pattern 10 6) else d335 (change pattern 10 6)) = d10 pattern
  rw [s1360, s1422]
  simp only [ite_self]
theorem s1424 (pattern : Ten) : d348 (change pattern 10 6) = d10 pattern := by
  change (if pattern.e then d337 (change pattern 10 6) else d214 (change pattern 10 6)) = d10 pattern
  rw [s1423, s1421]
  simp only [ite_self]
theorem s1425 (pattern : Ten) : d349 (change pattern 10 6) = d583 pattern := by
  change (if pattern.d then d348 (change pattern 10 6) else d347 (change pattern 10 6)) = d583 pattern
  rw [s1424, s1420]
  rfl
end NetHack.Sokoban41.Diagram
