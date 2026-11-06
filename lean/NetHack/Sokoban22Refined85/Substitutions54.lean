/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions53
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6480 (p : Pattern) : d1333 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1300 (change p 163 (some 162)) else d1332 (change p 163 (some 162))) = d4705 p
  rw [sub6445, sub6479]
  rfl
theorem sub6481 (p : Pattern) : d1334 (change p 163 (some 162)) = d4877 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1333 (change p 163 (some 162))) = d4877 p
  rw [sub6446, sub6480]
  rfl
theorem sub6482 (p : Pattern) : d1335 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1334 (change p 163 (some 162)) else d1331 (change p 163 (some 162))) = d4878 p
  rw [sub6481, sub6478]
  rfl
theorem sub6483 (p : Pattern) : d1336 (change p 163 (some 162)) = d4879 p := by
  change (if p 138 then d1335 (change p 163 (some 162)) else d1329 (change p 163 (some 162))) = d4879 p
  rw [sub6482, sub6476]
  rfl
theorem sub6484 (p : Pattern) : d1337 (change p 163 (some 162)) = d105 p := by
  change d1296 (change p 163 (some 162)) = d105 p
  exact sub6441 p
theorem sub6485 (p : Pattern) : d1338 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1337 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6484]
  rfl
theorem sub6486 (p : Pattern) : d1339 (change p 163 (some 162)) = d4876 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1338 (change p 163 (some 162))) = d4876 p
  rw [sub6446, sub6485]
  rfl
theorem sub6487 (p : Pattern) : d1340 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1334 (change p 163 (some 162)) else d1339 (change p 163 (some 162))) = d4878 p
  rw [sub6481, sub6486]
  rfl
theorem sub6488 (p : Pattern) : d1341 (change p 163 (some 162)) = d4880 p := by
  change (if p 138 then d12 (change p 163 (some 162)) else d1340 (change p 163 (some 162))) = d4880 p
  rw [sub6261, sub6487]
  rfl
theorem sub6489 (p : Pattern) : d1342 (change p 163 (some 162)) = d4881 p := by
  change (if p 116 then d1341 (change p 163 (some 162)) else d1336 (change p 163 (some 162))) = d4881 p
  rw [sub6488, sub6483]
  rfl
theorem sub6490 (p : Pattern) : d1343 (change p 163 (some 162)) = d4881 p := by
  change (if p 115 then d1342 (change p 163 (some 162)) else d1318 (change p 163 (some 162))) = d4881 p
  rw [sub6489, sub6466]
  simp only [ite_self]
theorem sub6491 (p : Pattern) : d1344 (change p 163 (some 162)) = d4882 p := by
  change (if p 71 then d1343 (change p 163 (some 162)) else d1236 (change p 163 (some 162))) = d4882 p
  rw [sub6490, sub6367]
  rfl
theorem sub6492 (p : Pattern) : d1345 (change p 163 (some 162)) = d4883 p := by
  change (if p 49 then d1344 (change p 163 (some 162)) else d1270 (change p 163 (some 162))) = d4883 p
  rw [sub6491, sub6401]
  rfl
theorem sub6493 (p : Pattern) : d1346 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1181 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6315]
  rfl
theorem sub6494 (p : Pattern) : d1348 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6495 (p : Pattern) : d1349 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d1348 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6494]
  simp only [ite_self]
theorem sub6496 (p : Pattern) : d1350 (change p 163 (some 162)) = d4862 p := by
  change (if p 160 then d1349 (change p 163 (some 162)) else d1346 (change p 163 (some 162))) = d4862 p
  rw [sub6495, sub6493]
  rfl
theorem sub6497 (p : Pattern) : d1351 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1350 (change p 163 (some 162)) else d1264 (change p 163 (some 162))) = d4863 p
  rw [sub6496, sub6395]
  rfl
theorem sub6498 (p : Pattern) : d1352 (change p 163 (some 162)) = d4864 p := by
  change (if p 138 then d1351 (change p 163 (some 162)) else d1262 (change p 163 (some 162))) = d4864 p
  rw [sub6497, sub6393]
  rfl
theorem sub6499 (p : Pattern) : d1353 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1350 (change p 163 (some 162)) else d1224 (change p 163 (some 162))) = d4863 p
  rw [sub6496, sub6355]
  rfl
theorem sub6500 (p : Pattern) : d1354 (change p 163 (some 162)) = d4867 p := by
  change (if p 138 then d12 (change p 163 (some 162)) else d1353 (change p 163 (some 162))) = d4867 p
  rw [sub6261, sub6499]
  rfl
theorem sub6501 (p : Pattern) : d1355 (change p 163 (some 162)) = d4868 p := by
  change (if p 116 then d1354 (change p 163 (some 162)) else d1352 (change p 163 (some 162))) = d4868 p
  rw [sub6500, sub6498]
  rfl
theorem sub6502 (p : Pattern) : d1356 (change p 163 (some 162)) = d4869 p := by
  change (if p 115 then d1355 (change p 163 (some 162)) else d1259 (change p 163 (some 162))) = d4869 p
  rw [sub6501, sub6390]
  rfl
theorem sub6503 (p : Pattern) : d1357 (change p 163 (some 162)) = d4869 p := by
  change (if p 71 then d1356 (change p 163 (some 162)) else d1236 (change p 163 (some 162))) = d4869 p
  rw [sub6502, sub6367]
  simp only [ite_self]
theorem sub6504 (p : Pattern) : d1358 (change p 163 (some 162)) = d132 p := by
  change d1289 (change p 163 (some 162)) = d132 p
  exact sub6448 p
theorem sub6505 (p : Pattern) : d1359 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1300 (change p 163 (some 162)) else d1358 (change p 163 (some 162))) = d4705 p
  rw [sub6445, sub6504]
  rfl
theorem sub6506 (p : Pattern) : d1360 (change p 163 (some 162)) = d4874 p := by
  change (if p 160 then d1293 (change p 163 (some 162)) else d1359 (change p 163 (some 162))) = d4874 p
  rw [sub6438, sub6505]
  rfl
theorem sub6507 (p : Pattern) : d1361 (change p 163 (some 162)) = d4875 p := by
  change (if p 141 then d1360 (change p 163 (some 162)) else d1282 (change p 163 (some 162))) = d4875 p
  rw [sub6506, sub6424]
  rfl
theorem sub6508 (p : Pattern) : d1362 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1334 (change p 163 (some 162)) else d1302 (change p 163 (some 162))) = d4878 p
  rw [sub6481, sub6447]
  rfl
theorem sub6509 (p : Pattern) : d1363 (change p 163 (some 162)) = d4879 p := by
  change (if p 138 then d1362 (change p 163 (some 162)) else d1361 (change p 163 (some 162))) = d4879 p
  rw [sub6508, sub6507]
  rfl
theorem sub6510 (p : Pattern) : d1364 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1334 (change p 163 (some 162)) else d1311 (change p 163 (some 162))) = d4878 p
  rw [sub6481, sub6456]
  rfl
theorem sub6511 (p : Pattern) : d1365 (change p 163 (some 162)) = d4880 p := by
  change (if p 138 then d162 (change p 163 (some 162)) else d1364 (change p 163 (some 162))) = d4880 p
  rw [sub6464, sub6510]
  rfl
theorem sub6512 (p : Pattern) : d1366 (change p 163 (some 162)) = d4881 p := by
  change (if p 116 then d1365 (change p 163 (some 162)) else d1363 (change p 163 (some 162))) = d4881 p
  rw [sub6511, sub6509]
  rfl
theorem sub6513 (p : Pattern) : d1367 (change p 163 (some 162)) = d105 p := by
  change d1296 (change p 163 (some 162)) = d105 p
  exact sub6441 p
theorem sub6514 (p : Pattern) : d1368 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1367 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6513]
  rfl
theorem sub6515 (p : Pattern) : d268 (change p 163 (some 162)) = d268 p := by
  change (if p 204 then d116 (change p 163 (some 162)) else d103 (change p 163 (some 162))) = d268 p
  rw [sub6427, sub6404]
  rfl
theorem sub6516 (p : Pattern) : d272 (change p 163 (some 162)) = d272 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d268 (change p 163 (some 162))) = d272 p
  rw [sub6261, sub6515]
  rfl
theorem sub6517 (p : Pattern) : d1370 (change p 163 (some 162)) = d272 p := by
  change d272 (change p 163 (some 162)) = d272 p
  exact sub6516 p
theorem sub6518 (p : Pattern) : d1371 (change p 163 (some 162)) = d272 p := by
  change d1370 (change p 163 (some 162)) = d272 p
  exact sub6517 p
theorem sub6519 (p : Pattern) : d277 (change p 163 (some 162)) = d277 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d59 (change p 163 (some 162))) = d277 p
  rw [sub6261, sub6412]
  rfl
theorem sub6520 (p : Pattern) : d278 (change p 163 (some 162)) = d277 p := by
  change d277 (change p 163 (some 162)) = d277 p
  exact sub6519 p
theorem sub6521 (p : Pattern) : d1372 (change p 163 (some 162)) = d277 p := by
  change d278 (change p 163 (some 162)) = d277 p
  exact sub6520 p
theorem sub6522 (p : Pattern) : d1373 (change p 163 (some 162)) = d4884 p := by
  change (if p 161 then d1372 (change p 163 (some 162)) else d1371 (change p 163 (some 162))) = d4884 p
  rw [sub6521, sub6518]
  rfl
theorem sub6523 (p : Pattern) : d1374 (change p 163 (some 162)) = d4885 p := by
  change (if p 160 then d1373 (change p 163 (some 162)) else d1368 (change p 163 (some 162))) = d4885 p
  rw [sub6522, sub6514]
  rfl
theorem sub6524 (p : Pattern) : d5 (change p 163 (some 162)) = d5 p := by
  rfl
theorem sub6525 (p : Pattern) : d106 (change p 163 (some 162)) = d106 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d5 (change p 163 (some 162))) = d106 p
  rw [sub6261, sub6524]
  rfl
theorem sub6526 (p : Pattern) : d107 (change p 163 (some 162)) = d107 p := by
  change (if p 246 then d106 (change p 163 (some 162)) else d5 (change p 163 (some 162))) = d107 p
  rw [sub6525, sub6524]
  rfl
theorem sub6527 (p : Pattern) : d282 (change p 163 (some 162)) = d282 p := by
  change (if p 204 then d107 (change p 163 (some 162)) else d116 (change p 163 (some 162))) = d282 p
  rw [sub6526, sub6427]
  rfl
theorem sub6528 (p : Pattern) : d283 (change p 163 (some 162)) = d283 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d282 (change p 163 (some 162))) = d283 p
  rw [sub6261, sub6527]
  rfl
theorem sub6529 (p : Pattern) : d1375 (change p 163 (some 162)) = d283 p := by
  change d283 (change p 163 (some 162)) = d283 p
  exact sub6528 p
theorem sub6530 (p : Pattern) : d1376 (change p 163 (some 162)) = d283 p := by
  change d1375 (change p 163 (some 162)) = d283 p
  exact sub6529 p
theorem sub6531 (p : Pattern) : d1377 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6532 (p : Pattern) : d1378 (change p 163 (some 162)) = d4886 p := by
  change (if p 161 then d1377 (change p 163 (some 162)) else d1376 (change p 163 (some 162))) = d4886 p
  rw [sub6531, sub6530]
  rfl
theorem sub6533 (p : Pattern) : d1379 (change p 163 (some 162)) = d4887 p := by
  change (if p 160 then d1378 (change p 163 (some 162)) else d1333 (change p 163 (some 162))) = d4887 p
  rw [sub6532, sub6480]
  rfl
theorem sub6534 (p : Pattern) : d1380 (change p 163 (some 162)) = d4888 p := by
  change (if p 141 then d1379 (change p 163 (some 162)) else d1374 (change p 163 (some 162))) = d4888 p
  rw [sub6533, sub6523]
  rfl
theorem sub6535 (p : Pattern) : d269 (change p 163 (some 162)) = d269 p := by
  change (if p 182 then d117 (change p 163 (some 162)) else d268 (change p 163 (some 162))) = d269 p
  rw [sub6428, sub6515]
  rfl
theorem sub6536 (p : Pattern) : d1369 (change p 163 (some 162)) = d269 p := by
  change d269 (change p 163 (some 162)) = d269 p
  exact sub6535 p
theorem sub6537 (p : Pattern) : d1381 (change p 163 (some 162)) = d269 p := by
  change d1369 (change p 163 (some 162)) = d269 p
  exact sub6536 p
theorem sub6538 (p : Pattern) : d1382 (change p 163 (some 162)) = d277 p := by
  change d278 (change p 163 (some 162)) = d277 p
  exact sub6520 p
theorem sub6539 (p : Pattern) : d1383 (change p 163 (some 162)) = d4889 p := by
  change (if p 161 then d1382 (change p 163 (some 162)) else d1381 (change p 163 (some 162))) = d4889 p
  rw [sub6538, sub6537]
  rfl
theorem sub6540 (p : Pattern) : d1384 (change p 163 (some 162)) = d4890 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1383 (change p 163 (some 162))) = d4890 p
  rw [sub6446, sub6539]
  rfl
theorem sub6541 (p : Pattern) : d108 (change p 163 (some 162)) = d108 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d107 (change p 163 (some 162))) = d108 p
  rw [sub6261, sub6526]
  rfl
theorem sub6542 (p : Pattern) : d298 (change p 163 (some 162)) = d298 p := by
  change (if p 182 then d108 (change p 163 (some 162)) else d282 (change p 163 (some 162))) = d298 p
  rw [sub6541, sub6527]
  rfl
theorem sub6543 (p : Pattern) : d1385 (change p 163 (some 162)) = d298 p := by
  change d298 (change p 163 (some 162)) = d298 p
  exact sub6542 p
theorem sub6544 (p : Pattern) : d1386 (change p 163 (some 162)) = d298 p := by
  change d1385 (change p 163 (some 162)) = d298 p
  exact sub6543 p
theorem sub6545 (p : Pattern) : d1387 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6546 (p : Pattern) : d1388 (change p 163 (some 162)) = d4891 p := by
  change (if p 161 then d1387 (change p 163 (some 162)) else d1386 (change p 163 (some 162))) = d4891 p
  rw [sub6545, sub6544]
  rfl
theorem sub6547 (p : Pattern) : d213 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6548 (p : Pattern) : d1389 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d213 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6547]
  simp only [ite_self]
theorem sub6549 (p : Pattern) : d1390 (change p 163 (some 162)) = d4892 p := by
  change (if p 160 then d1389 (change p 163 (some 162)) else d1388 (change p 163 (some 162))) = d4892 p
  rw [sub6548, sub6546]
  rfl
theorem sub6550 (p : Pattern) : d1391 (change p 163 (some 162)) = d4893 p := by
  change (if p 141 then d1390 (change p 163 (some 162)) else d1384 (change p 163 (some 162))) = d4893 p
  rw [sub6549, sub6540]
  rfl
theorem sub6551 (p : Pattern) : d1392 (change p 163 (some 162)) = d4894 p := by
  change (if p 138 then d1391 (change p 163 (some 162)) else d1380 (change p 163 (some 162))) = d4894 p
  rw [sub6550, sub6534]
  rfl
theorem sub6552 (p : Pattern) : d1393 (change p 163 (some 162)) = d4895 p := by
  change (if p 138 then d12 (change p 163 (some 162)) else d1391 (change p 163 (some 162))) = d4895 p
  rw [sub6261, sub6550]
  rfl
theorem sub6553 (p : Pattern) : d1394 (change p 163 (some 162)) = d4896 p := by
  change (if p 116 then d1393 (change p 163 (some 162)) else d1392 (change p 163 (some 162))) = d4896 p
  rw [sub6552, sub6551]
  rfl
theorem sub6554 (p : Pattern) : d1395 (change p 163 (some 162)) = d4897 p := by
  change (if p 115 then d1394 (change p 163 (some 162)) else d1366 (change p 163 (some 162))) = d4897 p
  rw [sub6553, sub6512]
  rfl
theorem sub6555 (p : Pattern) : d1396 (change p 163 (some 162)) = d4898 p := by
  change (if p 71 then d1395 (change p 163 (some 162)) else d1236 (change p 163 (some 162))) = d4898 p
  rw [sub6554, sub6367]
  rfl
theorem sub6556 (p : Pattern) : d1397 (change p 163 (some 162)) = d4899 p := by
  change (if p 49 then d1396 (change p 163 (some 162)) else d1357 (change p 163 (some 162))) = d4899 p
  rw [sub6555, sub6503]
  rfl
theorem sub6557 (p : Pattern) : d1398 (change p 163 (some 162)) = d4900 p := by
  change (if p 48 then d1397 (change p 163 (some 162)) else d1345 (change p 163 (some 162))) = d4900 p
  rw [sub6556, sub6492]
  rfl
theorem sub6558 (p : Pattern) : d0 (change p 10000 (some 224)) = d0 p := by
  rfl
theorem sub6559 (p : Pattern) : d12 (change p 10000 (some 224)) = d12 p := by
  rfl
theorem sub6560 (p : Pattern) : d13 (change p 10000 (some 224)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d0 (change p 10000 (some 224))) = d13 p
  rw [sub6559, sub6558]
  rfl
theorem sub6561 (p : Pattern) : d14 (change p 10000 (some 224)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 224)) else d0 (change p 10000 (some 224))) = d14 p
  rw [sub6560, sub6558]
  rfl
theorem sub6562 (p : Pattern) : d15 (change p 10000 (some 224)) = d15 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d15 p
  rw [sub6559, sub6561]
  rfl
theorem sub6563 (p : Pattern) : d16 (change p 10000 (some 224)) = d16 p := by
  change (if p 182 then d15 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d16 p
  rw [sub6562, sub6561]
  rfl
theorem sub6564 (p : Pattern) : d4 (change p 10000 (some 224)) = d4 p := by
  rfl
theorem sub6565 (p : Pattern) : d17 (change p 10000 (some 224)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d4 (change p 10000 (some 224))) = d17 p
  rw [sub6559, sub6564]
  rfl
theorem sub6566 (p : Pattern) : d18 (change p 10000 (some 224)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 224)) else d4 (change p 10000 (some 224))) = d18 p
  rw [sub6565, sub6564]
  rfl
theorem sub6567 (p : Pattern) : d19 (change p 10000 (some 224)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d18 (change p 10000 (some 224))) = d19 p
  rw [sub6559, sub6566]
  rfl
theorem sub6568 (p : Pattern) : d20 (change p 10000 (some 224)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 224)) else d18 (change p 10000 (some 224))) = d20 p
  rw [sub6567, sub6566]
  rfl
theorem sub6569 (p : Pattern) : d21 (change p 10000 (some 224)) = d21 p := by
  change (if p 163 then d20 (change p 10000 (some 224)) else d16 (change p 10000 (some 224))) = d21 p
  rw [sub6568, sub6563]
  rfl
theorem sub6570 (p : Pattern) : d22 (change p 10000 (some 224)) = d22 p := by
  change (if p 162 then d21 (change p 10000 (some 224)) else d16 (change p 10000 (some 224))) = d22 p
  rw [sub6569, sub6563]
  rfl
theorem sub6571 (p : Pattern) : d9 (change p 10000 (some 224)) = d9 p := by
  rfl
theorem sub6572 (p : Pattern) : d23 (change p 10000 (some 224)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d9 (change p 10000 (some 224))) = d23 p
  rw [sub6559, sub6571]
  rfl
theorem sub6573 (p : Pattern) : d24 (change p 10000 (some 224)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 224)) else d9 (change p 10000 (some 224))) = d24 p
  rw [sub6572, sub6571]
  rfl
theorem sub6574 (p : Pattern) : d25 (change p 10000 (some 224)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d24 (change p 10000 (some 224))) = d25 p
  rw [sub6559, sub6573]
  rfl
theorem sub6575 (p : Pattern) : d26 (change p 10000 (some 224)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 224)) else d24 (change p 10000 (some 224))) = d26 p
  rw [sub6574, sub6573]
  rfl
theorem sub6576 (p : Pattern) : d27 (change p 10000 (some 224)) = d27 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d26 (change p 10000 (some 224))) = d27 p
  rw [sub6559, sub6575]
  rfl
theorem sub6577 (p : Pattern) : d28 (change p 10000 (some 224)) = d28 p := by
  change (if p 162 then d27 (change p 10000 (some 224)) else d21 (change p 10000 (some 224))) = d28 p
  rw [sub6576, sub6569]
  rfl
theorem sub6578 (p : Pattern) : d29 (change p 10000 (some 224)) = d29 p := by
  change (if p 161 then d28 (change p 10000 (some 224)) else d22 (change p 10000 (some 224))) = d29 p
  rw [sub6577, sub6570]
  rfl
theorem sub6579 (p : Pattern) : d2 (change p 10000 (some 224)) = d2 p := by
  rfl
theorem sub6580 (p : Pattern) : d30 (change p 10000 (some 224)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d2 (change p 10000 (some 224))) = d30 p
  rw [sub6559, sub6579]
  rfl
theorem sub6581 (p : Pattern) : d31 (change p 10000 (some 224)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 224)) else d2 (change p 10000 (some 224))) = d31 p
  rw [sub6580, sub6579]
  rfl
theorem sub6582 (p : Pattern) : d32 (change p 10000 (some 224)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d31 (change p 10000 (some 224))) = d32 p
  rw [sub6559, sub6581]
  rfl
theorem sub6583 (p : Pattern) : d33 (change p 10000 (some 224)) = d33 p := by
  change (if p 182 then d32 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d33 p
  rw [sub6582, sub6561]
  rfl
theorem sub6584 (p : Pattern) : d6 (change p 10000 (some 224)) = d6 p := by
  rfl
theorem sub6585 (p : Pattern) : d34 (change p 10000 (some 224)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d6 (change p 10000 (some 224))) = d34 p
  rw [sub6559, sub6584]
  rfl
theorem sub6586 (p : Pattern) : d35 (change p 10000 (some 224)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 224)) else d6 (change p 10000 (some 224))) = d35 p
  rw [sub6585, sub6584]
  rfl
theorem sub6587 (p : Pattern) : d36 (change p 10000 (some 224)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d35 (change p 10000 (some 224))) = d36 p
  rw [sub6559, sub6586]
  rfl
theorem sub6588 (p : Pattern) : d37 (change p 10000 (some 224)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d37 p
  rw [sub6587, sub6561]
  rfl
theorem sub6589 (p : Pattern) : d38 (change p 10000 (some 224)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 224)) else d33 (change p 10000 (some 224))) = d38 p
  rw [sub6588, sub6583]
  rfl
theorem sub6590 (p : Pattern) : d11 (change p 10000 (some 224)) = d11 p := by
  rfl
theorem sub6591 (p : Pattern) : d39 (change p 10000 (some 224)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d11 (change p 10000 (some 224))) = d39 p
  rw [sub6559, sub6590]
  rfl
theorem sub6592 (p : Pattern) : d40 (change p 10000 (some 224)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 224)) else d11 (change p 10000 (some 224))) = d40 p
  rw [sub6591, sub6590]
  rfl
theorem sub6593 (p : Pattern) : d41 (change p 10000 (some 224)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d40 (change p 10000 (some 224))) = d41 p
  rw [sub6559, sub6592]
  rfl
theorem sub6594 (p : Pattern) : d42 (change p 10000 (some 224)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d42 p
  rw [sub6593, sub6561]
  rfl
theorem sub6595 (p : Pattern) : d43 (change p 10000 (some 224)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d18 (change p 10000 (some 224))) = d43 p
  rw [sub6559, sub6566]
  rfl
theorem sub6596 (p : Pattern) : d44 (change p 10000 (some 224)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 224)) else d42 (change p 10000 (some 224))) = d44 p
  rw [sub6595, sub6594]
  rfl
theorem sub6597 (p : Pattern) : d45 (change p 10000 (some 224)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 224)) else d38 (change p 10000 (some 224))) = d45 p
  rw [sub6596, sub6589]
  rfl
theorem sub6598 (p : Pattern) : d46 (change p 10000 (some 224)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d14 (change p 10000 (some 224))) = d46 p
  rw [sub6559, sub6561]
  rfl
theorem sub6599 (p : Pattern) : d47 (change p 10000 (some 224)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 224)) else d46 (change p 10000 (some 224))) = d47 p
  rw [sub6595, sub6598]
  rfl
end NetHack.Sokoban22Refined85
