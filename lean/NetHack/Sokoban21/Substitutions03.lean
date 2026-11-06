/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions02
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s450 (pattern : Twelve) : d64 (change pattern 12 3) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 12 3) else d34 (change pattern 12 3)) = d64 pattern
  rw [s449, s420]
  rfl
theorem s451 (pattern : Twelve) : d86 (change pattern 12 3) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 12 3) else d66 (change pattern 12 3)) = d86 pattern
  rw [s450, s448]
  rfl
theorem s452 (pattern : Twelve) : d99 (change pattern 12 3) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 12 3) else d85 (change pattern 12 3)) = d99 pattern
  rw [s451, s446]
  rfl
theorem s453 (pattern : Twelve) : d107 (change pattern 12 3) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 12 3) else d97 (change pattern 12 3)) = d107 pattern
  rw [s452, s443]
  rfl
theorem s454 (pattern : Twelve) : d112 (change pattern 12 3) = d107 pattern := by
  change d107 (change pattern 12 3) = d107 pattern
  exact s453 pattern
theorem s455 (pattern : Twelve) : d109 (change pattern 12 3) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d99 (change pattern 12 3)) = d109 pattern
  rw [s424, s452]
  rfl
theorem s456 (pattern : Twelve) : d113 (change pattern 12 3) = d109 pattern := by
  change d109 (change pattern 12 3) = d109 pattern
  exact s455 pattern
theorem s457 (pattern : Twelve) : d115 (change pattern 12 3) = d1881 pattern := by
  change (if pattern.c then d113 (change pattern 12 3) else d112 (change pattern 12 3)) = d1881 pattern
  rw [s456, s454]
  rfl
theorem s458 (pattern : Twelve) : d116 (change pattern 12 3) = d1882 pattern := by
  change (if pattern.g then d115 (change pattern 12 3) else d114 (change pattern 12 3)) = d1882 pattern
  rw [s457, s441]
  rfl
theorem s459 (pattern : Twelve) : d814 (change pattern 12 3) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 3) else d7 (change pattern 12 3)) = d814 pattern
  rw [s409, s411]
  rfl
theorem s460 (pattern : Twelve) : d816 (change pattern 12 3) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 3) else d814 (change pattern 12 3)) = d816 pattern
  rw [s409, s459]
  rfl
theorem s461 (pattern : Twelve) : d824 (change pattern 12 3) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 3) else d27 (change pattern 12 3)) = d824 pattern
  rw [s460, s413]
  rfl
theorem s462 (pattern : Twelve) : d838 (change pattern 12 3) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 12 3) else d0 (change pattern 12 3)) = d838 pattern
  rw [s461, s408]
  rfl
theorem s463 (pattern : Twelve) : d4 (change pattern 12 3) = d4 pattern := by
  rfl
theorem s464 (pattern : Twelve) : d16 (change pattern 12 3) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 3) else d2 (change pattern 12 3)) = d16 pattern
  rw [s463, s416]
  rfl
theorem s465 (pattern : Twelve) : d5 (change pattern 12 3) = d5 pattern := by
  rfl
theorem s466 (pattern : Twelve) : d12 (change pattern 12 3) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 3) else d3 (change pattern 12 3)) = d12 pattern
  rw [s465, s417]
  rfl
theorem s467 (pattern : Twelve) : d25 (change pattern 12 3) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 3) else d16 (change pattern 12 3)) = d25 pattern
  rw [s466, s464]
  rfl
theorem s468 (pattern : Twelve) : d817 (change pattern 12 3) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 3) else d19 (change pattern 12 3)) = d817 pattern
  rw [s467, s423]
  rfl
theorem s469 (pattern : Twelve) : d42 (change pattern 12 3) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d25 (change pattern 12 3)) = d42 pattern
  rw [s424, s467]
  rfl
theorem s470 (pattern : Twelve) : d825 (change pattern 12 3) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 3) else d817 (change pattern 12 3)) = d825 pattern
  rw [s469, s468]
  rfl
theorem s471 (pattern : Twelve) : d839 (change pattern 12 3) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 12 3) else d17 (change pattern 12 3)) = d839 pattern
  rw [s470, s412]
  rfl
theorem s472 (pattern : Twelve) : d853 (change pattern 12 3) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 12 3) else d838 (change pattern 12 3)) = d853 pattern
  rw [s471, s462]
  rfl
theorem s473 (pattern : Twelve) : d818 (change pattern 12 3) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d814 (change pattern 12 3)) = d818 pattern
  rw [s424, s459]
  rfl
theorem s474 (pattern : Twelve) : d826 (change pattern 12 3) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 12 3) else d34 (change pattern 12 3)) = d826 pattern
  rw [s473, s420]
  rfl
theorem s475 (pattern : Twelve) : d840 (change pattern 12 3) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 12 3) else d56 (change pattern 12 3)) = d840 pattern
  rw [s474, s431]
  rfl
theorem s476 (pattern : Twelve) : d827 (change pattern 12 3) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 12 3) else d34 (change pattern 12 3)) = d827 pattern
  rw [s432, s420]
  rfl
theorem s477 (pattern : Twelve) : d841 (change pattern 12 3) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 12 3) else d827 (change pattern 12 3)) = d841 pattern
  rw [s470, s476]
  rfl
theorem s478 (pattern : Twelve) : d854 (change pattern 12 3) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 12 3) else d840 (change pattern 12 3)) = d854 pattern
  rw [s477, s475]
  rfl
theorem s479 (pattern : Twelve) : d861 (change pattern 12 3) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 12 3) else d853 (change pattern 12 3)) = d861 pattern
  rw [s478, s472]
  rfl
theorem s480 (pattern : Twelve) : d863 (change pattern 12 3) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d854 (change pattern 12 3)) = d863 pattern
  rw [s424, s478]
  rfl
theorem s481 (pattern : Twelve) : d867 (change pattern 12 3) = d863 pattern := by
  change d863 (change pattern 12 3) = d863 pattern
  exact s480 pattern
theorem s482 (pattern : Twelve) : d869 (change pattern 12 3) = d1883 pattern := by
  change (if pattern.c then d867 (change pattern 12 3) else d861 (change pattern 12 3)) = d1883 pattern
  rw [s481, s479]
  rfl
theorem s483 (pattern : Twelve) : d823 (change pattern 12 3) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 12 3) else d17 (change pattern 12 3)) = d823 pattern
  rw [s416, s412]
  rfl
theorem s484 (pattern : Twelve) : d846 (change pattern 12 3) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 12 3) else d823 (change pattern 12 3)) = d846 pattern
  rw [s470, s483]
  rfl
theorem s485 (pattern : Twelve) : d857 (change pattern 12 3) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 12 3) else d838 (change pattern 12 3)) = d857 pattern
  rw [s484, s462]
  rfl
theorem s486 (pattern : Twelve) : d832 (change pattern 12 3) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 12 3) else d34 (change pattern 12 3)) = d832 pattern
  rw [s444, s420]
  rfl
theorem s487 (pattern : Twelve) : d847 (change pattern 12 3) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 12 3) else d56 (change pattern 12 3)) = d847 pattern
  rw [s486, s431]
  rfl
theorem s488 (pattern : Twelve) : d833 (change pattern 12 3) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 12 3) else d34 (change pattern 12 3)) = d833 pattern
  rw [s447, s420]
  rfl
theorem s489 (pattern : Twelve) : d848 (change pattern 12 3) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 12 3) else d833 (change pattern 12 3)) = d848 pattern
  rw [s470, s488]
  rfl
theorem s490 (pattern : Twelve) : d858 (change pattern 12 3) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 12 3) else d847 (change pattern 12 3)) = d858 pattern
  rw [s489, s487]
  rfl
theorem s491 (pattern : Twelve) : d864 (change pattern 12 3) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 12 3) else d857 (change pattern 12 3)) = d864 pattern
  rw [s490, s485]
  rfl
theorem s492 (pattern : Twelve) : d866 (change pattern 12 3) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d858 (change pattern 12 3)) = d866 pattern
  rw [s424, s490]
  rfl
theorem s493 (pattern : Twelve) : d868 (change pattern 12 3) = d866 pattern := by
  change d866 (change pattern 12 3) = d866 pattern
  exact s492 pattern
theorem s494 (pattern : Twelve) : d870 (change pattern 12 3) = d1884 pattern := by
  change (if pattern.c then d868 (change pattern 12 3) else d864 (change pattern 12 3)) = d1884 pattern
  rw [s493, s491]
  rfl
theorem s495 (pattern : Twelve) : d871 (change pattern 12 3) = d1885 pattern := by
  change (if pattern.g then d870 (change pattern 12 3) else d869 (change pattern 12 3)) = d1885 pattern
  rw [s494, s482]
  rfl
theorem s496 (pattern : Twelve) : d8 (change pattern 12 3) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 3) else d1 (change pattern 12 3)) = d8 pattern
  rw [s416, s409]
  rfl
theorem s497 (pattern : Twelve) : d1275 (change pattern 12 3) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 3) else d7 (change pattern 12 3)) = d1275 pattern
  rw [s496, s411]
  rfl
theorem s498 (pattern : Twelve) : d872 (change pattern 12 3) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 3) else d1 (change pattern 12 3)) = d872 pattern
  rw [s496, s409]
  rfl
theorem s499 (pattern : Twelve) : d1278 (change pattern 12 3) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 3) else d1275 (change pattern 12 3)) = d1278 pattern
  rw [s498, s497]
  rfl
theorem s500 (pattern : Twelve) : d1284 (change pattern 12 3) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 3) else d1278 (change pattern 12 3)) = d1284 pattern
  rw [s498, s499]
  rfl
theorem s501 (pattern : Twelve) : d1293 (change pattern 12 3) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 12 3) else d17 (change pattern 12 3)) = d1293 pattern
  rw [s500, s412]
  rfl
theorem s502 (pattern : Twelve) : d1294 (change pattern 12 3) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d19 (change pattern 12 3)) = d1294 pattern
  rw [s424, s423]
  rfl
theorem s503 (pattern : Twelve) : d1305 (change pattern 12 3) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 12 3) else d1293 (change pattern 12 3)) = d1305 pattern
  rw [s502, s501]
  rfl
theorem s504 (pattern : Twelve) : d117 (change pattern 12 3) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 3) else d3 (change pattern 12 3)) = d117 pattern
  rw [s463, s417]
  rfl
theorem s505 (pattern : Twelve) : d1276 (change pattern 12 3) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 3) else d9 (change pattern 12 3)) = d1276 pattern
  rw [s504, s418]
  rfl
theorem s506 (pattern : Twelve) : d1279 (change pattern 12 3) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 3) else d1275 (change pattern 12 3)) = d1279 pattern
  rw [s505, s497]
  rfl
theorem s507 (pattern : Twelve) : d1280 (change pattern 12 3) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d872 (change pattern 12 3)) = d1280 pattern
  rw [s424, s498]
  rfl
theorem s508 (pattern : Twelve) : d1285 (change pattern 12 3) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 3) else d1279 (change pattern 12 3)) = d1285 pattern
  rw [s507, s506]
  rfl
theorem s509 (pattern : Twelve) : d1295 (change pattern 12 3) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 12 3) else d827 (change pattern 12 3)) = d1295 pattern
  rw [s508, s476]
  rfl
theorem s510 (pattern : Twelve) : d1286 (change pattern 12 3) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 12 3) else d817 (change pattern 12 3)) = d1286 pattern
  rw [s425, s468]
  rfl
theorem s511 (pattern : Twelve) : d1296 (change pattern 12 3) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d1286 (change pattern 12 3)) = d1296 pattern
  rw [s424, s510]
  rfl
theorem s512 (pattern : Twelve) : d1306 (change pattern 12 3) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 12 3) else d1295 (change pattern 12 3)) = d1306 pattern
  rw [s511, s509]
  rfl
theorem s513 (pattern : Twelve) : d1313 (change pattern 12 3) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 12 3) else d1305 (change pattern 12 3)) = d1313 pattern
  rw [s512, s503]
  rfl
theorem s514 (pattern : Twelve) : d1315 (change pattern 12 3) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d1306 (change pattern 12 3)) = d1315 pattern
  rw [s424, s512]
  rfl
theorem s515 (pattern : Twelve) : d1319 (change pattern 12 3) = d1315 pattern := by
  change d1315 (change pattern 12 3) = d1315 pattern
  exact s514 pattern
theorem s516 (pattern : Twelve) : d1321 (change pattern 12 3) = d1886 pattern := by
  change (if pattern.c then d1319 (change pattern 12 3) else d1313 (change pattern 12 3)) = d1886 pattern
  rw [s515, s513]
  rfl
theorem s517 (pattern : Twelve) : d1283 (change pattern 12 3) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 12 3) else d19 (change pattern 12 3)) = d1283 pattern
  rw [s419, s423]
  rfl
theorem s518 (pattern : Twelve) : d1301 (change pattern 12 3) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d1283 (change pattern 12 3)) = d1301 pattern
  rw [s424, s517]
  rfl
theorem s519 (pattern : Twelve) : d1309 (change pattern 12 3) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 12 3) else d1293 (change pattern 12 3)) = d1309 pattern
  rw [s518, s501]
  rfl
theorem s520 (pattern : Twelve) : d1290 (change pattern 12 3) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 12 3) else d817 (change pattern 12 3)) = d1290 pattern
  rw [s449, s468]
  rfl
theorem s521 (pattern : Twelve) : d1302 (change pattern 12 3) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d1290 (change pattern 12 3)) = d1302 pattern
  rw [s424, s520]
  rfl
theorem s522 (pattern : Twelve) : d1310 (change pattern 12 3) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 12 3) else d1295 (change pattern 12 3)) = d1310 pattern
  rw [s521, s509]
  rfl
theorem s523 (pattern : Twelve) : d1316 (change pattern 12 3) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 12 3) else d1309 (change pattern 12 3)) = d1316 pattern
  rw [s522, s519]
  rfl
theorem s524 (pattern : Twelve) : d1318 (change pattern 12 3) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d1310 (change pattern 12 3)) = d1318 pattern
  rw [s424, s522]
  rfl
theorem s525 (pattern : Twelve) : d1320 (change pattern 12 3) = d1318 pattern := by
  change d1318 (change pattern 12 3) = d1318 pattern
  exact s524 pattern
theorem s526 (pattern : Twelve) : d1322 (change pattern 12 3) = d1887 pattern := by
  change (if pattern.c then d1320 (change pattern 12 3) else d1316 (change pattern 12 3)) = d1887 pattern
  rw [s525, s523]
  rfl
theorem s527 (pattern : Twelve) : d1323 (change pattern 12 3) = d1888 pattern := by
  change (if pattern.g then d1322 (change pattern 12 3) else d1321 (change pattern 12 3)) = d1888 pattern
  rw [s526, s516]
  rfl
theorem s528 (pattern : Twelve) : d1324 (change pattern 12 3) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 3) else d11 (change pattern 12 3)) = d1324 pattern
  rw [s464, s422]
  rfl
theorem s529 (pattern : Twelve) : d1649 (change pattern 12 3) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 3) else d19 (change pattern 12 3)) = d1649 pattern
  rw [s528, s423]
  rfl
theorem s530 (pattern : Twelve) : d1650 (change pattern 12 3) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d25 (change pattern 12 3)) = d1650 pattern
  rw [s424, s467]
  rfl
theorem s531 (pattern : Twelve) : d1656 (change pattern 12 3) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 3) else d1649 (change pattern 12 3)) = d1656 pattern
  rw [s530, s529]
  rfl
theorem s532 (pattern : Twelve) : d13 (change pattern 12 3) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 3) else d4 (change pattern 12 3)) = d13 pattern
  rw [s424, s463]
  rfl
theorem s533 (pattern : Twelve) : d20 (change pattern 12 3) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 3) else d12 (change pattern 12 3)) = d20 pattern
  rw [s532, s466]
  rfl
theorem s534 (pattern : Twelve) : d1644 (change pattern 12 3) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 3) else d1324 (change pattern 12 3)) = d1644 pattern
  rw [s533, s528]
  rfl
theorem s535 (pattern : Twelve) : d1645 (change pattern 12 3) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d1324 (change pattern 12 3)) = d1645 pattern
  rw [s424, s528]
  rfl
theorem s536 (pattern : Twelve) : d1647 (change pattern 12 3) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 3) else d1644 (change pattern 12 3)) = d1647 pattern
  rw [s535, s534]
  rfl
theorem s537 (pattern : Twelve) : d1651 (change pattern 12 3) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 12 3) else d1286 (change pattern 12 3)) = d1651 pattern
  rw [s536, s510]
  rfl
theorem s538 (pattern : Twelve) : d14 (change pattern 12 3) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 3) else d5 (change pattern 12 3)) = d14 pattern
  rw [s424, s465]
  rfl
theorem s539 (pattern : Twelve) : d21 (change pattern 12 3) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 3) else d13 (change pattern 12 3)) = d21 pattern
  rw [s538, s532]
  rfl
theorem s540 (pattern : Twelve) : d821 (change pattern 12 3) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 3) else d25 (change pattern 12 3)) = d821 pattern
  rw [s539, s467]
  rfl
theorem s541 (pattern : Twelve) : d1289 (change pattern 12 3) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 12 3) else d821 (change pattern 12 3)) = d1289 pattern
  rw [s469, s540]
  rfl
theorem s542 (pattern : Twelve) : d1300 (change pattern 12 3) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 12 3) else d1289 (change pattern 12 3)) = d1300 pattern
  rw [s424, s541]
  rfl
theorem s543 (pattern : Twelve) : d1657 (change pattern 12 3) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 12 3) else d1651 (change pattern 12 3)) = d1657 pattern
  rw [s542, s537]
  rfl
theorem s544 (pattern : Twelve) : d1660 (change pattern 12 3) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 12 3) else d1656 (change pattern 12 3)) = d1660 pattern
  rw [s543, s531]
  rfl
theorem s545 (pattern : Twelve) : d1662 (change pattern 12 3) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d1657 (change pattern 12 3)) = d1662 pattern
  rw [s424, s543]
  rfl
theorem s546 (pattern : Twelve) : d1663 (change pattern 12 3) = d1662 pattern := by
  change d1662 (change pattern 12 3) = d1662 pattern
  exact s545 pattern
theorem s547 (pattern : Twelve) : d1664 (change pattern 12 3) = d1889 pattern := by
  change (if pattern.c then d1663 (change pattern 12 3) else d1660 (change pattern 12 3)) = d1889 pattern
  rw [s546, s544]
  rfl
theorem s548 (pattern : Twelve) : d0 (change pattern 3 12) = d0 pattern := by
  rfl
theorem s549 (pattern : Twelve) : d1 (change pattern 3 12) = d1 pattern := by
  rfl
theorem s550 (pattern : Twelve) : d7 (change pattern 3 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 3 12) else d0 (change pattern 3 12)) = d7 pattern
  rw [s549, s548]
  rfl
theorem s551 (pattern : Twelve) : d17 (change pattern 3 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 3 12) else d0 (change pattern 3 12)) = d17 pattern
  rw [s550, s548]
  rfl
theorem s552 (pattern : Twelve) : d27 (change pattern 3 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 3 12) else d17 (change pattern 3 12)) = d27 pattern
  rw [s549, s551]
  rfl
theorem s553 (pattern : Twelve) : d814 (change pattern 3 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 3 12) else d7 (change pattern 3 12)) = d814 pattern
  rw [s549, s550]
  rfl
theorem s554 (pattern : Twelve) : d816 (change pattern 3 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 3 12) else d814 (change pattern 3 12)) = d816 pattern
  rw [s549, s553]
  rfl
theorem s555 (pattern : Twelve) : d824 (change pattern 3 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 3 12) else d27 (change pattern 3 12)) = d824 pattern
  rw [s554, s552]
  rfl
theorem s556 (pattern : Twelve) : d838 (change pattern 3 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 3 12) else d0 (change pattern 3 12)) = d838 pattern
  rw [s555, s548]
  rfl
theorem s557 (pattern : Twelve) : d2 (change pattern 3 12) = d2 pattern := by
  rfl
theorem s558 (pattern : Twelve) : d10 (change pattern 3 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 3 12) else d0 (change pattern 3 12)) = d10 pattern
  rw [s557, s548]
  rfl
theorem s559 (pattern : Twelve) : d3 (change pattern 3 12) = d3 pattern := by
  rfl
theorem s560 (pattern : Twelve) : d11 (change pattern 3 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 3 12) else d1 (change pattern 3 12)) = d11 pattern
  rw [s559, s549]
  rfl
theorem s561 (pattern : Twelve) : d19 (change pattern 3 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 3 12) else d10 (change pattern 3 12)) = d19 pattern
  rw [s560, s558]
  rfl
theorem s562 (pattern : Twelve) : d4 (change pattern 3 12) = d4 pattern := by
  rfl
theorem s563 (pattern : Twelve) : d16 (change pattern 3 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 3 12) else d2 (change pattern 3 12)) = d16 pattern
  rw [s562, s557]
  rfl
theorem s564 (pattern : Twelve) : d5 (change pattern 3 12) = d5 pattern := by
  rfl
theorem s565 (pattern : Twelve) : d12 (change pattern 3 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 3 12) else d3 (change pattern 3 12)) = d12 pattern
  rw [s564, s559]
  rfl
theorem s566 (pattern : Twelve) : d25 (change pattern 3 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 3 12) else d16 (change pattern 3 12)) = d25 pattern
  rw [s565, s563]
  rfl
theorem s567 (pattern : Twelve) : d817 (change pattern 3 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 3 12) else d19 (change pattern 3 12)) = d817 pattern
  rw [s566, s561]
  rfl
theorem s568 (pattern : Twelve) : d6 (change pattern 3 12) = d6 pattern := by
  rfl
theorem s569 (pattern : Twelve) : d42 (change pattern 3 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d25 (change pattern 3 12)) = d42 pattern
  rw [s568, s566]
  rfl
theorem s570 (pattern : Twelve) : d825 (change pattern 3 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 3 12) else d817 (change pattern 3 12)) = d825 pattern
  rw [s569, s567]
  rfl
theorem s571 (pattern : Twelve) : d839 (change pattern 3 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d17 (change pattern 3 12)) = d839 pattern
  rw [s570, s551]
  rfl
theorem s572 (pattern : Twelve) : d853 (change pattern 3 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 3 12) else d838 (change pattern 3 12)) = d853 pattern
  rw [s571, s556]
  rfl
theorem s573 (pattern : Twelve) : d30 (change pattern 3 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 3 12) else d0 (change pattern 3 12)) = d30 pattern
  rw [s557, s548]
  rfl
theorem s574 (pattern : Twelve) : d35 (change pattern 3 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d0 (change pattern 3 12)) = d35 pattern
  rw [s568, s548]
  rfl
theorem s575 (pattern : Twelve) : d56 (change pattern 3 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 3 12) else d30 (change pattern 3 12)) = d56 pattern
  rw [s574, s573]
  rfl
theorem s576 (pattern : Twelve) : d9 (change pattern 3 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 3 12) else d2 (change pattern 3 12)) = d9 pattern
  rw [s559, s557]
  rfl
theorem s577 (pattern : Twelve) : d23 (change pattern 3 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 3 12) else d2 (change pattern 3 12)) = d23 pattern
  rw [s576, s557]
  rfl
theorem s578 (pattern : Twelve) : d34 (change pattern 3 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 3 12) else d17 (change pattern 3 12)) = d34 pattern
  rw [s577, s551]
  rfl
theorem s579 (pattern : Twelve) : d818 (change pattern 3 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d814 (change pattern 3 12)) = d818 pattern
  rw [s568, s553]
  rfl
theorem s580 (pattern : Twelve) : d826 (change pattern 3 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 3 12) else d34 (change pattern 3 12)) = d826 pattern
  rw [s579, s578]
  rfl
theorem s581 (pattern : Twelve) : d840 (change pattern 3 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 3 12) else d56 (change pattern 3 12)) = d840 pattern
  rw [s580, s575]
  rfl
theorem s582 (pattern : Twelve) : d36 (change pattern 3 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d17 (change pattern 3 12)) = d36 pattern
  rw [s568, s551]
  rfl
theorem s583 (pattern : Twelve) : d827 (change pattern 3 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 3 12) else d34 (change pattern 3 12)) = d827 pattern
  rw [s582, s578]
  rfl
theorem s584 (pattern : Twelve) : d841 (change pattern 3 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d827 (change pattern 3 12)) = d841 pattern
  rw [s570, s583]
  rfl
theorem s585 (pattern : Twelve) : d854 (change pattern 3 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 3 12) else d840 (change pattern 3 12)) = d854 pattern
  rw [s584, s581]
  rfl
theorem s586 (pattern : Twelve) : d861 (change pattern 3 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 3 12) else d853 (change pattern 3 12)) = d861 pattern
  rw [s585, s572]
  rfl
theorem s587 (pattern : Twelve) : d927 (change pattern 3 12) = d861 pattern := by
  change d861 (change pattern 3 12) = d861 pattern
  exact s586 pattern
theorem s588 (pattern : Twelve) : d819 (change pattern 3 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 3 12) else d814 (change pattern 3 12)) = d819 pattern
  rw [s559, s553]
  rfl
theorem s589 (pattern : Twelve) : d828 (change pattern 3 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 3 12) else d34 (change pattern 3 12)) = d828 pattern
  rw [s588, s578]
  rfl
theorem s590 (pattern : Twelve) : d842 (change pattern 3 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 3 12) else d30 (change pattern 3 12)) = d842 pattern
  rw [s589, s573]
  rfl
theorem s591 (pattern : Twelve) : d843 (change pattern 3 12) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d34 (change pattern 3 12)) = d843 pattern
  rw [s570, s578]
  rfl
theorem s592 (pattern : Twelve) : d855 (change pattern 3 12) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 3 12) else d842 (change pattern 3 12)) = d855 pattern
  rw [s591, s590]
  rfl
theorem s593 (pattern : Twelve) : d38 (change pattern 3 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 3 12) else d2 (change pattern 3 12)) = d38 pattern
  rw [s562, s557]
  rfl
theorem s594 (pattern : Twelve) : d39 (change pattern 3 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d2 (change pattern 3 12)) = d39 pattern
  rw [s568, s557]
  rfl
theorem s595 (pattern : Twelve) : d59 (change pattern 3 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 3 12) else d38 (change pattern 3 12)) = d59 pattern
  rw [s594, s593]
  rfl
theorem s596 (pattern : Twelve) : d15 (change pattern 3 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 3 12) else d4 (change pattern 3 12)) = d15 pattern
  rw [s564, s562]
  rfl
theorem s597 (pattern : Twelve) : d24 (change pattern 3 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 3 12) else d4 (change pattern 3 12)) = d24 pattern
  rw [s596, s562]
  rfl
theorem s598 (pattern : Twelve) : d41 (change pattern 3 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 3 12) else d23 (change pattern 3 12)) = d41 pattern
  rw [s597, s577]
  rfl
theorem s599 (pattern : Twelve) : d815 (change pattern 3 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 3 12) else d9 (change pattern 3 12)) = d815 pattern
  rw [s559, s576]
  rfl
end NetHack.Sokoban21.Diagram
