/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions42
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6450 (pattern : Twelve) : d1296 (change pattern 12 0) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1286 (change pattern 12 0)) = d1296 pattern
  rw [s6278, s6449]
  rfl
theorem s6451 (pattern : Twelve) : d1306 (change pattern 12 0) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 12 0) else d1295 (change pattern 12 0)) = d1306 pattern
  rw [s6450, s6448]
  rfl
theorem s6452 (pattern : Twelve) : d1313 (change pattern 12 0) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 12 0) else d1305 (change pattern 12 0)) = d1313 pattern
  rw [s6451, s6442]
  rfl
theorem s6453 (pattern : Twelve) : d119 (change pattern 12 0) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 0) else d3 (change pattern 12 0)) = d119 pattern
  rw [s6443, s6271]
  rfl
theorem s6454 (pattern : Twelve) : d1281 (change pattern 12 0) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 12 0) else d872 (change pattern 12 0)) = d1281 pattern
  rw [s6453, s6437]
  rfl
theorem s6455 (pattern : Twelve) : d1287 (change pattern 12 0) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 12 0) else d1279 (change pattern 12 0)) = d1287 pattern
  rw [s6454, s6445]
  rfl
theorem s6456 (pattern : Twelve) : d1297 (change pattern 12 0) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 12 0) else d34 (change pattern 12 0)) = d1297 pattern
  rw [s6455, s6300]
  rfl
theorem s6457 (pattern : Twelve) : d1298 (change pattern 12 0) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d817 (change pattern 12 0)) = d1298 pattern
  rw [s6278, s6382]
  rfl
theorem s6458 (pattern : Twelve) : d1307 (change pattern 12 0) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 12 0) else d1297 (change pattern 12 0)) = d1307 pattern
  rw [s6457, s6456]
  rfl
theorem s6459 (pattern : Twelve) : d1277 (change pattern 12 0) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 0) else d15 (change pattern 12 0)) = d1277 pattern
  rw [s6291, s6327]
  rfl
theorem s6460 (pattern : Twelve) : d1282 (change pattern 12 0) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 12 0) else d1276 (change pattern 12 0)) = d1282 pattern
  rw [s6459, s6444]
  rfl
theorem s6461 (pattern : Twelve) : d125 (change pattern 12 0) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d119 (change pattern 12 0)) = d125 pattern
  rw [s6278, s6453]
  rfl
theorem s6462 (pattern : Twelve) : d1288 (change pattern 12 0) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 12 0) else d1282 (change pattern 12 0)) = d1288 pattern
  rw [s6461, s6460]
  rfl
theorem s6463 (pattern : Twelve) : d1299 (change pattern 12 0) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 12 0) else d830 (change pattern 12 0)) = d1299 pattern
  rw [s6462, s6402]
  rfl
theorem s6464 (pattern : Twelve) : d1289 (change pattern 12 0) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 12 0) else d821 (change pattern 12 0)) = d1289 pattern
  rw [s6332, s6403]
  rfl
theorem s6465 (pattern : Twelve) : d1300 (change pattern 12 0) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1289 (change pattern 12 0)) = d1300 pattern
  rw [s6278, s6464]
  rfl
theorem s6466 (pattern : Twelve) : d1308 (change pattern 12 0) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 12 0) else d1299 (change pattern 12 0)) = d1308 pattern
  rw [s6465, s6463]
  rfl
theorem s6467 (pattern : Twelve) : d1314 (change pattern 12 0) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 12 0) else d1307 (change pattern 12 0)) = d1314 pattern
  rw [s6466, s6458]
  rfl
theorem s6468 (pattern : Twelve) : d1315 (change pattern 12 0) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1306 (change pattern 12 0)) = d1315 pattern
  rw [s6278, s6451]
  rfl
theorem s6469 (pattern : Twelve) : d1319 (change pattern 12 0) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 12 0) else d1314 (change pattern 12 0)) = d1319 pattern
  rw [s6468, s6467]
  rfl
theorem s6470 (pattern : Twelve) : d1321 (change pattern 12 0) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 12 0) else d1313 (change pattern 12 0)) = d1321 pattern
  rw [s6469, s6452]
  rfl
theorem s6471 (pattern : Twelve) : d1283 (change pattern 12 0) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 12 0) else d19 (change pattern 12 0)) = d1283 pattern
  rw [s6299, s6277]
  rfl
theorem s6472 (pattern : Twelve) : d1301 (change pattern 12 0) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1283 (change pattern 12 0)) = d1301 pattern
  rw [s6278, s6471]
  rfl
theorem s6473 (pattern : Twelve) : d1309 (change pattern 12 0) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 12 0) else d1293 (change pattern 12 0)) = d1309 pattern
  rw [s6472, s6440]
  rfl
theorem s6474 (pattern : Twelve) : d1290 (change pattern 12 0) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 12 0) else d817 (change pattern 12 0)) = d1290 pattern
  rw [s6324, s6382]
  rfl
theorem s6475 (pattern : Twelve) : d1302 (change pattern 12 0) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1290 (change pattern 12 0)) = d1302 pattern
  rw [s6278, s6474]
  rfl
theorem s6476 (pattern : Twelve) : d1310 (change pattern 12 0) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 12 0) else d1295 (change pattern 12 0)) = d1310 pattern
  rw [s6475, s6448]
  rfl
theorem s6477 (pattern : Twelve) : d1316 (change pattern 12 0) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 12 0) else d1309 (change pattern 12 0)) = d1316 pattern
  rw [s6476, s6473]
  rfl
theorem s6478 (pattern : Twelve) : d1291 (change pattern 12 0) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 12 0) else d817 (change pattern 12 0)) = d1291 pattern
  rw [s6329, s6382]
  rfl
theorem s6479 (pattern : Twelve) : d1303 (change pattern 12 0) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1291 (change pattern 12 0)) = d1303 pattern
  rw [s6278, s6478]
  rfl
theorem s6480 (pattern : Twelve) : d1311 (change pattern 12 0) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 12 0) else d1297 (change pattern 12 0)) = d1311 pattern
  rw [s6479, s6456]
  rfl
theorem s6481 (pattern : Twelve) : d1292 (change pattern 12 0) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 12 0) else d821 (change pattern 12 0)) = d1292 pattern
  rw [s6369, s6403]
  rfl
theorem s6482 (pattern : Twelve) : d1304 (change pattern 12 0) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d1292 (change pattern 12 0)) = d1304 pattern
  rw [s6278, s6481]
  rfl
theorem s6483 (pattern : Twelve) : d1312 (change pattern 12 0) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 12 0) else d1299 (change pattern 12 0)) = d1312 pattern
  rw [s6482, s6463]
  rfl
theorem s6484 (pattern : Twelve) : d1317 (change pattern 12 0) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 12 0) else d1311 (change pattern 12 0)) = d1317 pattern
  rw [s6483, s6480]
  rfl
theorem s6485 (pattern : Twelve) : d1318 (change pattern 12 0) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1310 (change pattern 12 0)) = d1318 pattern
  rw [s6278, s6476]
  rfl
theorem s6486 (pattern : Twelve) : d1320 (change pattern 12 0) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 12 0) else d1317 (change pattern 12 0)) = d1320 pattern
  rw [s6485, s6484]
  rfl
theorem s6487 (pattern : Twelve) : d1322 (change pattern 12 0) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 12 0) else d1316 (change pattern 12 0)) = d1322 pattern
  rw [s6486, s6477]
  rfl
theorem s6488 (pattern : Twelve) : d1323 (change pattern 12 0) = d1323 pattern := by
  change (if pattern.g then d1322 (change pattern 12 0) else d1321 (change pattern 12 0)) = d1323 pattern
  rw [s6487, s6470]
  rfl
theorem s6489 (pattern : Twelve) : d1324 (change pattern 12 0) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 0) else d11 (change pattern 12 0)) = d1324 pattern
  rw [s6330, s6276]
  rfl
theorem s6490 (pattern : Twelve) : d1649 (change pattern 12 0) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 0) else d19 (change pattern 12 0)) = d1649 pattern
  rw [s6489, s6277]
  rfl
theorem s6491 (pattern : Twelve) : d1650 (change pattern 12 0) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d25 (change pattern 12 0)) = d1650 pattern
  rw [s6278, s6331]
  rfl
theorem s6492 (pattern : Twelve) : d1656 (change pattern 12 0) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 0) else d1649 (change pattern 12 0)) = d1656 pattern
  rw [s6491, s6490]
  rfl
theorem s6493 (pattern : Twelve) : d1644 (change pattern 12 0) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 0) else d1324 (change pattern 12 0)) = d1644 pattern
  rw [s6288, s6489]
  rfl
theorem s6494 (pattern : Twelve) : d1645 (change pattern 12 0) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d1324 (change pattern 12 0)) = d1645 pattern
  rw [s6278, s6489]
  rfl
theorem s6495 (pattern : Twelve) : d1647 (change pattern 12 0) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 0) else d1644 (change pattern 12 0)) = d1647 pattern
  rw [s6494, s6493]
  rfl
theorem s6496 (pattern : Twelve) : d1651 (change pattern 12 0) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 12 0) else d1286 (change pattern 12 0)) = d1651 pattern
  rw [s6495, s6449]
  rfl
theorem s6497 (pattern : Twelve) : d1657 (change pattern 12 0) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 12 0) else d1651 (change pattern 12 0)) = d1657 pattern
  rw [s6465, s6496]
  rfl
theorem s6498 (pattern : Twelve) : d1660 (change pattern 12 0) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 12 0) else d1656 (change pattern 12 0)) = d1660 pattern
  rw [s6497, s6492]
  rfl
theorem s6499 (pattern : Twelve) : d1652 (change pattern 12 0) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 12 0) else d817 (change pattern 12 0)) = d1652 pattern
  rw [s6493, s6382]
  rfl
theorem s6500 (pattern : Twelve) : d1653 (change pattern 12 0) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d821 (change pattern 12 0)) = d1653 pattern
  rw [s6278, s6403]
  rfl
theorem s6501 (pattern : Twelve) : d1658 (change pattern 12 0) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 12 0) else d1652 (change pattern 12 0)) = d1658 pattern
  rw [s6500, s6499]
  rfl
theorem s6502 (pattern : Twelve) : d1646 (change pattern 12 0) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d20 (change pattern 12 0)) = d1646 pattern
  rw [s6296, s6288]
  rfl
theorem s6503 (pattern : Twelve) : d128 (change pattern 12 0) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d20 (change pattern 12 0)) = d128 pattern
  rw [s6278, s6288]
  rfl
theorem s6504 (pattern : Twelve) : d1648 (change pattern 12 0) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 12 0) else d1646 (change pattern 12 0)) = d1648 pattern
  rw [s6503, s6502]
  rfl
theorem s6505 (pattern : Twelve) : d1654 (change pattern 12 0) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 12 0) else d1289 (change pattern 12 0)) = d1654 pattern
  rw [s6504, s6464]
  rfl
theorem s6506 (pattern : Twelve) : d1655 (change pattern 12 0) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d822 (change pattern 12 0)) = d1655 pattern
  rw [s6278, s6404]
  rfl
theorem s6507 (pattern : Twelve) : d1659 (change pattern 12 0) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 12 0) else d1654 (change pattern 12 0)) = d1659 pattern
  rw [s6506, s6505]
  rfl
theorem s6508 (pattern : Twelve) : d1661 (change pattern 12 0) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 12 0) else d1658 (change pattern 12 0)) = d1661 pattern
  rw [s6507, s6501]
  rfl
theorem s6509 (pattern : Twelve) : d1662 (change pattern 12 0) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d1657 (change pattern 12 0)) = d1662 pattern
  rw [s6278, s6497]
  rfl
theorem s6510 (pattern : Twelve) : d1663 (change pattern 12 0) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 12 0) else d1661 (change pattern 12 0)) = d1663 pattern
  rw [s6509, s6508]
  rfl
theorem s6511 (pattern : Twelve) : d1664 (change pattern 12 0) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 12 0) else d1660 (change pattern 12 0)) = d1664 pattern
  rw [s6510, s6498]
  rfl
theorem s6512 (pattern : Twelve) : d0 (change pattern 12 1) = d0 pattern := by
  rfl
theorem s6513 (pattern : Twelve) : d1 (change pattern 12 1) = d1 pattern := by
  rfl
theorem s6514 (pattern : Twelve) : d26 (change pattern 12 1) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 1) else d0 (change pattern 12 1)) = d26 pattern
  rw [s6513, s6512]
  rfl
theorem s6515 (pattern : Twelve) : d7 (change pattern 12 1) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 1) else d0 (change pattern 12 1)) = d7 pattern
  rw [s6513, s6512]
  rfl
theorem s6516 (pattern : Twelve) : d17 (change pattern 12 1) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 1) else d0 (change pattern 12 1)) = d17 pattern
  rw [s6515, s6512]
  rfl
theorem s6517 (pattern : Twelve) : d27 (change pattern 12 1) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 1) else d17 (change pattern 12 1)) = d27 pattern
  rw [s6513, s6516]
  rfl
theorem s6518 (pattern : Twelve) : d50 (change pattern 12 1) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 1) else d26 (change pattern 12 1)) = d50 pattern
  rw [s6517, s6514]
  rfl
theorem s6519 (pattern : Twelve) : d72 (change pattern 12 1) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 12 1) else d0 (change pattern 12 1)) = d72 pattern
  rw [s6518, s6512]
  rfl
theorem s6520 (pattern : Twelve) : d2 (change pattern 12 1) = d2 pattern := by
  rfl
theorem s6521 (pattern : Twelve) : d8 (change pattern 12 1) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 1) else d1 (change pattern 12 1)) = d8 pattern
  rw [s6520, s6513]
  rfl
theorem s6522 (pattern : Twelve) : d3 (change pattern 12 1) = d3 pattern := by
  rfl
theorem s6523 (pattern : Twelve) : d9 (change pattern 12 1) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 1) else d2 (change pattern 12 1)) = d9 pattern
  rw [s6522, s6520]
  rfl
theorem s6524 (pattern : Twelve) : d18 (change pattern 12 1) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 12 1) else d8 (change pattern 12 1)) = d18 pattern
  rw [s6523, s6521]
  rfl
theorem s6525 (pattern : Twelve) : d28 (change pattern 12 1) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 12 1) else d17 (change pattern 12 1)) = d28 pattern
  rw [s6524, s6516]
  rfl
theorem s6526 (pattern : Twelve) : d10 (change pattern 12 1) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 1) else d0 (change pattern 12 1)) = d10 pattern
  rw [s6520, s6512]
  rfl
theorem s6527 (pattern : Twelve) : d11 (change pattern 12 1) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 1) else d1 (change pattern 12 1)) = d11 pattern
  rw [s6522, s6513]
  rfl
theorem s6528 (pattern : Twelve) : d19 (change pattern 12 1) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 1) else d10 (change pattern 12 1)) = d19 pattern
  rw [s6527, s6526]
  rfl
theorem s6529 (pattern : Twelve) : d6 (change pattern 12 1) = d6 pattern := by
  rfl
theorem s6530 (pattern : Twelve) : d29 (change pattern 12 1) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d19 (change pattern 12 1)) = d29 pattern
  rw [s6529, s6528]
  rfl
theorem s6531 (pattern : Twelve) : d51 (change pattern 12 1) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 12 1) else d28 (change pattern 12 1)) = d51 pattern
  rw [s6530, s6525]
  rfl
theorem s6532 (pattern : Twelve) : d73 (change pattern 12 1) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 12 1) else d0 (change pattern 12 1)) = d73 pattern
  rw [s6531, s6512]
  rfl
theorem s6533 (pattern : Twelve) : d91 (change pattern 12 1) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 12 1) else d72 (change pattern 12 1)) = d91 pattern
  rw [s6532, s6519]
  rfl
theorem s6534 (pattern : Twelve) : d30 (change pattern 12 1) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 1) else d0 (change pattern 12 1)) = d30 pattern
  rw [s6520, s6512]
  rfl
theorem s6535 (pattern : Twelve) : d5 (change pattern 12 1) = d5 pattern := by
  rfl
theorem s6536 (pattern : Twelve) : d12 (change pattern 12 1) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 1) else d3 (change pattern 12 1)) = d12 pattern
  rw [s6535, s6522]
  rfl
theorem s6537 (pattern : Twelve) : d4 (change pattern 12 1) = d4 pattern := by
  rfl
theorem s6538 (pattern : Twelve) : d13 (change pattern 12 1) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 1) else d4 (change pattern 12 1)) = d13 pattern
  rw [s6529, s6537]
  rfl
theorem s6539 (pattern : Twelve) : d20 (change pattern 12 1) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 1) else d12 (change pattern 12 1)) = d20 pattern
  rw [s6538, s6536]
  rfl
theorem s6540 (pattern : Twelve) : d31 (change pattern 12 1) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 12 1) else d0 (change pattern 12 1)) = d31 pattern
  rw [s6539, s6512]
  rfl
theorem s6541 (pattern : Twelve) : d52 (change pattern 12 1) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 12 1) else d30 (change pattern 12 1)) = d52 pattern
  rw [s6540, s6534]
  rfl
theorem s6542 (pattern : Twelve) : d14 (change pattern 12 1) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 1) else d5 (change pattern 12 1)) = d14 pattern
  rw [s6529, s6535]
  rfl
theorem s6543 (pattern : Twelve) : d21 (change pattern 12 1) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 1) else d13 (change pattern 12 1)) = d21 pattern
  rw [s6542, s6538]
  rfl
theorem s6544 (pattern : Twelve) : d32 (change pattern 12 1) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 12 1) else d17 (change pattern 12 1)) = d32 pattern
  rw [s6543, s6516]
  rfl
theorem s6545 (pattern : Twelve) : d53 (change pattern 12 1) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 12 1) else d30 (change pattern 12 1)) = d53 pattern
  rw [s6544, s6534]
  rfl
theorem s6546 (pattern : Twelve) : d74 (change pattern 12 1) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 12 1) else d52 (change pattern 12 1)) = d74 pattern
  rw [s6545, s6541]
  rfl
theorem s6547 (pattern : Twelve) : d22 (change pattern 12 1) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 1) else d14 (change pattern 12 1)) = d22 pattern
  rw [s6529, s6542]
  rfl
theorem s6548 (pattern : Twelve) : d33 (change pattern 12 1) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d0 (change pattern 12 1)) = d33 pattern
  rw [s6547, s6512]
  rfl
theorem s6549 (pattern : Twelve) : d54 (change pattern 12 1) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 12 1) else d30 (change pattern 12 1)) = d54 pattern
  rw [s6548, s6534]
  rfl
theorem s6550 (pattern : Twelve) : d23 (change pattern 12 1) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 1) else d2 (change pattern 12 1)) = d23 pattern
  rw [s6523, s6520]
  rfl
theorem s6551 (pattern : Twelve) : d34 (change pattern 12 1) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 1) else d17 (change pattern 12 1)) = d34 pattern
  rw [s6550, s6516]
  rfl
theorem s6552 (pattern : Twelve) : d55 (change pattern 12 1) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 1) else d34 (change pattern 12 1)) = d55 pattern
  rw [s6530, s6551]
  rfl
theorem s6553 (pattern : Twelve) : d75 (change pattern 12 1) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 12 1) else d54 (change pattern 12 1)) = d75 pattern
  rw [s6552, s6549]
  rfl
theorem s6554 (pattern : Twelve) : d92 (change pattern 12 1) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 12 1) else d74 (change pattern 12 1)) = d92 pattern
  rw [s6553, s6546]
  rfl
theorem s6555 (pattern : Twelve) : d102 (change pattern 12 1) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 12 1) else d91 (change pattern 12 1)) = d102 pattern
  rw [s6554, s6533]
  rfl
theorem s6556 (pattern : Twelve) : d76 (change pattern 12 1) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 12 1) else d0 (change pattern 12 1)) = d76 pattern
  rw [s6552, s6512]
  rfl
theorem s6557 (pattern : Twelve) : d93 (change pattern 12 1) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 12 1) else d72 (change pattern 12 1)) = d93 pattern
  rw [s6556, s6519]
  rfl
theorem s6558 (pattern : Twelve) : d35 (change pattern 12 1) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d0 (change pattern 12 1)) = d35 pattern
  rw [s6529, s6512]
  rfl
theorem s6559 (pattern : Twelve) : d56 (change pattern 12 1) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 1) else d30 (change pattern 12 1)) = d56 pattern
  rw [s6558, s6534]
  rfl
theorem s6560 (pattern : Twelve) : d36 (change pattern 12 1) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d17 (change pattern 12 1)) = d36 pattern
  rw [s6529, s6516]
  rfl
theorem s6561 (pattern : Twelve) : d57 (change pattern 12 1) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 12 1) else d30 (change pattern 12 1)) = d57 pattern
  rw [s6560, s6534]
  rfl
theorem s6562 (pattern : Twelve) : d77 (change pattern 12 1) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 12 1) else d56 (change pattern 12 1)) = d77 pattern
  rw [s6561, s6559]
  rfl
theorem s6563 (pattern : Twelve) : d78 (change pattern 12 1) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 12 1) else d56 (change pattern 12 1)) = d78 pattern
  rw [s6552, s6559]
  rfl
theorem s6564 (pattern : Twelve) : d94 (change pattern 12 1) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 12 1) else d77 (change pattern 12 1)) = d94 pattern
  rw [s6563, s6562]
  rfl
theorem s6565 (pattern : Twelve) : d103 (change pattern 12 1) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 12 1) else d93 (change pattern 12 1)) = d103 pattern
  rw [s6564, s6557]
  rfl
theorem s6566 (pattern : Twelve) : d110 (change pattern 12 1) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 12 1) else d102 (change pattern 12 1)) = d110 pattern
  rw [s6565, s6555]
  rfl
theorem s6567 (pattern : Twelve) : d37 (change pattern 12 1) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d17 (change pattern 12 1)) = d37 pattern
  rw [s6522, s6516]
  rfl
theorem s6568 (pattern : Twelve) : d58 (change pattern 12 1) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 12 1) else d30 (change pattern 12 1)) = d58 pattern
  rw [s6567, s6534]
  rfl
theorem s6569 (pattern : Twelve) : d79 (change pattern 12 1) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 12 1) else d30 (change pattern 12 1)) = d79 pattern
  rw [s6568, s6534]
  rfl
theorem s6570 (pattern : Twelve) : d80 (change pattern 12 1) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 12 1) else d30 (change pattern 12 1)) = d80 pattern
  rw [s6552, s6534]
  rfl
theorem s6571 (pattern : Twelve) : d95 (change pattern 12 1) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 12 1) else d79 (change pattern 12 1)) = d95 pattern
  rw [s6570, s6569]
  rfl
theorem s6572 (pattern : Twelve) : d38 (change pattern 12 1) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 1) else d2 (change pattern 12 1)) = d38 pattern
  rw [s6537, s6520]
  rfl
theorem s6573 (pattern : Twelve) : d39 (change pattern 12 1) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d2 (change pattern 12 1)) = d39 pattern
  rw [s6529, s6520]
  rfl
theorem s6574 (pattern : Twelve) : d59 (change pattern 12 1) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 12 1) else d38 (change pattern 12 1)) = d59 pattern
  rw [s6573, s6572]
  rfl
theorem s6575 (pattern : Twelve) : d40 (change pattern 12 1) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d23 (change pattern 12 1)) = d40 pattern
  rw [s6529, s6550]
  rfl
theorem s6576 (pattern : Twelve) : d60 (change pattern 12 1) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 12 1) else d38 (change pattern 12 1)) = d60 pattern
  rw [s6575, s6572]
  rfl
theorem s6577 (pattern : Twelve) : d81 (change pattern 12 1) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 12 1) else d59 (change pattern 12 1)) = d81 pattern
  rw [s6576, s6574]
  rfl
theorem s6578 (pattern : Twelve) : d15 (change pattern 12 1) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 1) else d4 (change pattern 12 1)) = d15 pattern
  rw [s6535, s6537]
  rfl
theorem s6579 (pattern : Twelve) : d24 (change pattern 12 1) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 1) else d4 (change pattern 12 1)) = d24 pattern
  rw [s6578, s6537]
  rfl
theorem s6580 (pattern : Twelve) : d41 (change pattern 12 1) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 12 1) else d23 (change pattern 12 1)) = d41 pattern
  rw [s6579, s6550]
  rfl
theorem s6581 (pattern : Twelve) : d16 (change pattern 12 1) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 1) else d2 (change pattern 12 1)) = d16 pattern
  rw [s6537, s6520]
  rfl
theorem s6582 (pattern : Twelve) : d25 (change pattern 12 1) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 1) else d16 (change pattern 12 1)) = d25 pattern
  rw [s6536, s6581]
  rfl
theorem s6583 (pattern : Twelve) : d42 (change pattern 12 1) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d25 (change pattern 12 1)) = d42 pattern
  rw [s6529, s6582]
  rfl
theorem s6584 (pattern : Twelve) : d61 (change pattern 12 1) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 12 1) else d41 (change pattern 12 1)) = d61 pattern
  rw [s6583, s6580]
  rfl
theorem s6585 (pattern : Twelve) : d82 (change pattern 12 1) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 12 1) else d59 (change pattern 12 1)) = d82 pattern
  rw [s6584, s6574]
  rfl
theorem s6586 (pattern : Twelve) : d96 (change pattern 12 1) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 12 1) else d81 (change pattern 12 1)) = d96 pattern
  rw [s6585, s6577]
  rfl
theorem s6587 (pattern : Twelve) : d104 (change pattern 12 1) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 12 1) else d95 (change pattern 12 1)) = d104 pattern
  rw [s6586, s6571]
  rfl
theorem s6588 (pattern : Twelve) : d105 (change pattern 12 1) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d94 (change pattern 12 1)) = d105 pattern
  rw [s6529, s6564]
  rfl
theorem s6589 (pattern : Twelve) : d111 (change pattern 12 1) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 12 1) else d104 (change pattern 12 1)) = d111 pattern
  rw [s6588, s6587]
  rfl
theorem s6590 (pattern : Twelve) : d114 (change pattern 12 1) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 12 1) else d110 (change pattern 12 1)) = d114 pattern
  rw [s6589, s6566]
  rfl
theorem s6591 (pattern : Twelve) : d97 (change pattern 12 1) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 12 1) else d72 (change pattern 12 1)) = d97 pattern
  rw [s6570, s6519]
  rfl
theorem s6592 (pattern : Twelve) : d43 (change pattern 12 1) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 12 1) else d1 (change pattern 12 1)) = d43 pattern
  rw [s6543, s6513]
  rfl
theorem s6593 (pattern : Twelve) : d62 (change pattern 12 1) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 12 1) else d30 (change pattern 12 1)) = d62 pattern
  rw [s6592, s6534]
  rfl
theorem s6594 (pattern : Twelve) : d83 (change pattern 12 1) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 12 1) else d52 (change pattern 12 1)) = d83 pattern
  rw [s6593, s6541]
  rfl
theorem s6595 (pattern : Twelve) : d44 (change pattern 12 1) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d2 (change pattern 12 1)) = d44 pattern
  rw [s6547, s6520]
  rfl
theorem s6596 (pattern : Twelve) : d63 (change pattern 12 1) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 12 1) else d30 (change pattern 12 1)) = d63 pattern
  rw [s6595, s6534]
  rfl
theorem s6597 (pattern : Twelve) : d64 (change pattern 12 1) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 12 1) else d34 (change pattern 12 1)) = d64 pattern
  rw [s6575, s6551]
  rfl
theorem s6598 (pattern : Twelve) : d84 (change pattern 12 1) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 12 1) else d63 (change pattern 12 1)) = d84 pattern
  rw [s6597, s6596]
  rfl
theorem s6599 (pattern : Twelve) : d98 (change pattern 12 1) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 12 1) else d83 (change pattern 12 1)) = d98 pattern
  rw [s6598, s6594]
  rfl
end NetHack.Sokoban21.Diagram
