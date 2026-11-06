/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions36
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5550 (pattern : Twelve) : d876 (change pattern 1 12) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 1 12) else d19 (change pattern 1 12)) = d876 pattern
  rw [s5505, s5460]
  rfl
theorem s5551 (pattern : Twelve) : d883 (change pattern 1 12) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 1 12) else d876 (change pattern 1 12)) = d883 pattern
  rw [s5468, s5550]
  rfl
theorem s5552 (pattern : Twelve) : d891 (change pattern 1 12) = d891 pattern := by
  change (if pattern.f then d883 (change pattern 1 12) else d17 (change pattern 1 12)) = d891 pattern
  rw [s5551, s5450]
  rfl
theorem s5553 (pattern : Twelve) : d898 (change pattern 1 12) = d898 pattern := by
  change (if pattern.e then d891 (change pattern 1 12) else d890 (change pattern 1 12)) = d898 pattern
  rw [s5552, s5549]
  rfl
theorem s5554 (pattern : Twelve) : d877 (change pattern 1 12) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 1 12) else d17 (change pattern 1 12)) = d877 pattern
  rw [s5497, s5450]
  rfl
theorem s5555 (pattern : Twelve) : d884 (change pattern 1 12) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 1 12) else d877 (change pattern 1 12)) = d884 pattern
  rw [s5478, s5554]
  rfl
theorem s5556 (pattern : Twelve) : d892 (change pattern 1 12) = d892 pattern := by
  change (if pattern.f then d884 (change pattern 1 12) else d56 (change pattern 1 12)) = d892 pattern
  rw [s5555, s5474]
  rfl
theorem s5557 (pattern : Twelve) : d893 (change pattern 1 12) = d893 pattern := by
  change (if pattern.f then d883 (change pattern 1 12) else d827 (change pattern 1 12)) = d893 pattern
  rw [s5551, s5482]
  rfl
theorem s5558 (pattern : Twelve) : d899 (change pattern 1 12) = d899 pattern := by
  change (if pattern.e then d893 (change pattern 1 12) else d892 (change pattern 1 12)) = d899 pattern
  rw [s5557, s5556]
  rfl
theorem s5559 (pattern : Twelve) : d902 (change pattern 1 12) = d902 pattern := by
  change (if pattern.j then d899 (change pattern 1 12) else d898 (change pattern 1 12)) = d902 pattern
  rw [s5558, s5553]
  rfl
theorem s5560 (pattern : Twelve) : d878 (change pattern 1 12) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 1 12) else d814 (change pattern 1 12)) = d878 pattern
  rw [s5495, s5452]
  rfl
theorem s5561 (pattern : Twelve) : d885 (change pattern 1 12) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 1 12) else d877 (change pattern 1 12)) = d885 pattern
  rw [s5560, s5554]
  rfl
theorem s5562 (pattern : Twelve) : d894 (change pattern 1 12) = d894 pattern := by
  change (if pattern.f then d885 (change pattern 1 12) else d30 (change pattern 1 12)) = d894 pattern
  rw [s5561, s5472]
  rfl
theorem s5563 (pattern : Twelve) : d117 (change pattern 1 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 1 12) else d3 (change pattern 1 12)) = d117 pattern
  rw [s5461, s5458]
  rfl
theorem s5564 (pattern : Twelve) : d119 (change pattern 1 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 1 12) else d3 (change pattern 1 12)) = d119 pattern
  rw [s5563, s5458]
  rfl
theorem s5565 (pattern : Twelve) : d879 (change pattern 1 12) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 1 12) else d17 (change pattern 1 12)) = d879 pattern
  rw [s5564, s5450]
  rfl
theorem s5566 (pattern : Twelve) : d886 (change pattern 1 12) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 1 12) else d34 (change pattern 1 12)) = d886 pattern
  rw [s5565, s5477]
  rfl
theorem s5567 (pattern : Twelve) : d895 (change pattern 1 12) = d895 pattern := by
  change (if pattern.f then d883 (change pattern 1 12) else d886 (change pattern 1 12)) = d895 pattern
  rw [s5551, s5566]
  rfl
theorem s5568 (pattern : Twelve) : d900 (change pattern 1 12) = d900 pattern := by
  change (if pattern.e then d895 (change pattern 1 12) else d894 (change pattern 1 12)) = d900 pattern
  rw [s5567, s5562]
  rfl
theorem s5569 (pattern : Twelve) : d22 (change pattern 1 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 1 12) else d14 (change pattern 1 12)) = d22 pattern
  rw [s5467, s5504]
  rfl
theorem s5570 (pattern : Twelve) : d127 (change pattern 1 12) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d23 (change pattern 1 12)) = d127 pattern
  rw [s5569, s5476]
  rfl
theorem s5571 (pattern : Twelve) : d873 (change pattern 1 12) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 1 12) else d117 (change pattern 1 12)) = d873 pattern
  rw [s5494, s5563]
  rfl
theorem s5572 (pattern : Twelve) : d880 (change pattern 1 12) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d873 (change pattern 1 12)) = d880 pattern
  rw [s5467, s5571]
  rfl
theorem s5573 (pattern : Twelve) : d887 (change pattern 1 12) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 1 12) else d127 (change pattern 1 12)) = d887 pattern
  rw [s5572, s5570]
  rfl
theorem s5574 (pattern : Twelve) : d896 (change pattern 1 12) = d896 pattern := by
  change (if pattern.f then d887 (change pattern 1 12) else d59 (change pattern 1 12)) = d896 pattern
  rw [s5573, s5493]
  rfl
theorem s5575 (pattern : Twelve) : d118 (change pattern 1 12) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 1 12) else d5 (change pattern 1 12)) = d118 pattern
  rw [s5504, s5463]
  rfl
theorem s5576 (pattern : Twelve) : d881 (change pattern 1 12) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 1 12) else d23 (change pattern 1 12)) = d881 pattern
  rw [s5575, s5476]
  rfl
theorem s5577 (pattern : Twelve) : d125 (change pattern 1 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d119 (change pattern 1 12)) = d125 pattern
  rw [s5467, s5564]
  rfl
theorem s5578 (pattern : Twelve) : d888 (change pattern 1 12) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 1 12) else d881 (change pattern 1 12)) = d888 pattern
  rw [s5577, s5576]
  rfl
theorem s5579 (pattern : Twelve) : d889 (change pattern 1 12) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 1 12) else d42 (change pattern 1 12)) = d889 pattern
  rw [s5467, s5468]
  rfl
theorem s5580 (pattern : Twelve) : d897 (change pattern 1 12) = d897 pattern := by
  change (if pattern.f then d889 (change pattern 1 12) else d888 (change pattern 1 12)) = d897 pattern
  rw [s5579, s5578]
  rfl
theorem s5581 (pattern : Twelve) : d901 (change pattern 1 12) = d901 pattern := by
  change (if pattern.e then d897 (change pattern 1 12) else d896 (change pattern 1 12)) = d901 pattern
  rw [s5580, s5574]
  rfl
theorem s5582 (pattern : Twelve) : d903 (change pattern 1 12) = d903 pattern := by
  change (if pattern.j then d901 (change pattern 1 12) else d900 (change pattern 1 12)) = d903 pattern
  rw [s5581, s5568]
  rfl
theorem s5583 (pattern : Twelve) : d904 (change pattern 1 12) = d904 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d899 (change pattern 1 12)) = d904 pattern
  rw [s5467, s5558]
  rfl
theorem s5584 (pattern : Twelve) : d905 (change pattern 1 12) = d905 pattern := by
  change (if pattern.d then d904 (change pattern 1 12) else d903 (change pattern 1 12)) = d905 pattern
  rw [s5583, s5582]
  rfl
theorem s5585 (pattern : Twelve) : d906 (change pattern 1 12) = d906 pattern := by
  change (if pattern.c then d905 (change pattern 1 12) else d902 (change pattern 1 12)) = d906 pattern
  rw [s5584, s5559]
  rfl
theorem s5586 (pattern : Twelve) : d779 (change pattern 1 12) = d779 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d23 (change pattern 1 12)) = d779 pattern
  rw [s5458, s5476]
  rfl
theorem s5587 (pattern : Twelve) : d1247 (change pattern 1 12) = d1247 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d815 (change pattern 1 12)) = d1247 pattern
  rw [s5458, s5497]
  rfl
theorem s5588 (pattern : Twelve) : d1249 (change pattern 1 12) = d1249 pattern := by
  change (if pattern.h then d1247 (change pattern 1 12) else d779 (change pattern 1 12)) = d1249 pattern
  rw [s5587, s5586]
  rfl
theorem s5589 (pattern : Twelve) : d1253 (change pattern 1 12) = d1253 pattern := by
  change (if pattern.f then d1249 (change pattern 1 12) else d2 (change pattern 1 12)) = d1253 pattern
  rw [s5588, s5456]
  rfl
theorem s5590 (pattern : Twelve) : d1248 (change pattern 1 12) = d1248 pattern := by
  change (if pattern.i then d4 (change pattern 1 12) else d23 (change pattern 1 12)) = d1248 pattern
  rw [s5461, s5476]
  rfl
theorem s5591 (pattern : Twelve) : d1254 (change pattern 1 12) = d1254 pattern := by
  change (if pattern.f then d831 (change pattern 1 12) else d1248 (change pattern 1 12)) = d1254 pattern
  rw [s5508, s5590]
  rfl
theorem s5592 (pattern : Twelve) : d1258 (change pattern 1 12) = d1258 pattern := by
  change (if pattern.e then d1254 (change pattern 1 12) else d1253 (change pattern 1 12)) = d1258 pattern
  rw [s5591, s5589]
  rfl
theorem s5593 (pattern : Twelve) : d1261 (change pattern 1 12) = d1261 pattern := by
  change (if pattern.j then d860 (change pattern 1 12) else d1258 (change pattern 1 12)) = d1261 pattern
  rw [s5537, s5592]
  rfl
theorem s5594 (pattern : Twelve) : d780 (change pattern 1 12) = d780 pattern := by
  change (if pattern.i then d5 (change pattern 1 12) else d3 (change pattern 1 12)) = d780 pattern
  rw [s5463, s5458]
  rfl
theorem s5595 (pattern : Twelve) : d1250 (change pattern 1 12) = d1250 pattern := by
  change (if pattern.h then d780 (change pattern 1 12) else d41 (change pattern 1 12)) = d1250 pattern
  rw [s5594, s5496]
  rfl
theorem s5596 (pattern : Twelve) : d1255 (change pattern 1 12) = d1255 pattern := by
  change (if pattern.f then d1250 (change pattern 1 12) else d38 (change pattern 1 12)) = d1255 pattern
  rw [s5595, s5491]
  rfl
theorem s5597 (pattern : Twelve) : d1259 (change pattern 1 12) = d1259 pattern := by
  change (if pattern.e then d852 (change pattern 1 12) else d1255 (change pattern 1 12)) = d1259 pattern
  rw [s5536, s5596]
  rfl
theorem s5598 (pattern : Twelve) : d49 (change pattern 1 12) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d24 (change pattern 1 12)) = d49 pattern
  rw [s5467, s5495]
  rfl
theorem s5599 (pattern : Twelve) : d781 (change pattern 1 12) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d5 (change pattern 1 12)) = d781 pattern
  rw [s5467, s5463]
  rfl
theorem s5600 (pattern : Twelve) : d1251 (change pattern 1 12) = d1251 pattern := by
  change (if pattern.h then d781 (change pattern 1 12) else d49 (change pattern 1 12)) = d1251 pattern
  rw [s5599, s5598]
  rfl
theorem s5601 (pattern : Twelve) : d1256 (change pattern 1 12) = d1256 pattern := by
  change (if pattern.f then d1251 (change pattern 1 12) else d48 (change pattern 1 12)) = d1256 pattern
  rw [s5600, s5534]
  rfl
theorem s5602 (pattern : Twelve) : d787 (change pattern 1 12) = d787 pattern := by
  change (if pattern.h then d6 (change pattern 1 12) else d49 (change pattern 1 12)) = d787 pattern
  rw [s5467, s5598]
  rfl
theorem s5603 (pattern : Twelve) : d1252 (change pattern 1 12) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 1 12) else d822 (change pattern 1 12)) = d1252 pattern
  rw [s5467, s5507]
  rfl
theorem s5604 (pattern : Twelve) : d1257 (change pattern 1 12) = d1257 pattern := by
  change (if pattern.f then d1252 (change pattern 1 12) else d787 (change pattern 1 12)) = d1257 pattern
  rw [s5603, s5602]
  rfl
theorem s5605 (pattern : Twelve) : d1260 (change pattern 1 12) = d1260 pattern := by
  change (if pattern.e then d1257 (change pattern 1 12) else d1256 (change pattern 1 12)) = d1260 pattern
  rw [s5604, s5601]
  rfl
theorem s5606 (pattern : Twelve) : d1262 (change pattern 1 12) = d1262 pattern := by
  change (if pattern.j then d1260 (change pattern 1 12) else d1259 (change pattern 1 12)) = d1262 pattern
  rw [s5605, s5597]
  rfl
theorem s5607 (pattern : Twelve) : d1263 (change pattern 1 12) = d1263 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d860 (change pattern 1 12)) = d1263 pattern
  rw [s5467, s5537]
  rfl
theorem s5608 (pattern : Twelve) : d1264 (change pattern 1 12) = d1264 pattern := by
  change (if pattern.d then d1263 (change pattern 1 12) else d1262 (change pattern 1 12)) = d1264 pattern
  rw [s5607, s5606]
  rfl
theorem s5609 (pattern : Twelve) : d1265 (change pattern 1 12) = d1265 pattern := by
  change (if pattern.c then d1264 (change pattern 1 12) else d1261 (change pattern 1 12)) = d1265 pattern
  rw [s5608, s5593]
  rfl
theorem s5610 (pattern : Twelve) : d1266 (change pattern 1 12) = d1266 pattern := by
  change (if pattern.g then d1265 (change pattern 1 12) else d906 (change pattern 1 12)) = d1266 pattern
  rw [s5609, s5585]
  rfl
theorem s5611 (pattern : Twelve) : d1272 (change pattern 1 12) = d1266 pattern := by
  change d1266 (change pattern 1 12) = d1266 pattern
  exact s5610 pattern
theorem s5612 (pattern : Twelve) : d1273 (change pattern 1 12) = d1267 pattern := by
  change (if pattern.a then d1272 (change pattern 1 12) else d1271 (change pattern 1 12)) = d1267 pattern
  rw [s5611, s5543]
  rfl
theorem s5613 (pattern : Twelve) : d1275 (change pattern 1 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 1 12) else d7 (change pattern 1 12)) = d1275 pattern
  rw [s5544, s5449]
  rfl
theorem s5614 (pattern : Twelve) : d1278 (change pattern 1 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 1 12) else d1275 (change pattern 1 12)) = d1278 pattern
  rw [s5545, s5613]
  rfl
theorem s5615 (pattern : Twelve) : d1284 (change pattern 1 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 1 12) else d1278 (change pattern 1 12)) = d1284 pattern
  rw [s5545, s5614]
  rfl
theorem s5616 (pattern : Twelve) : d1293 (change pattern 1 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 1 12) else d17 (change pattern 1 12)) = d1293 pattern
  rw [s5615, s5450]
  rfl
theorem s5617 (pattern : Twelve) : d1294 (change pattern 1 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d19 (change pattern 1 12)) = d1294 pattern
  rw [s5467, s5460]
  rfl
theorem s5618 (pattern : Twelve) : d1305 (change pattern 1 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 1 12) else d1293 (change pattern 1 12)) = d1305 pattern
  rw [s5617, s5616]
  rfl
theorem s5619 (pattern : Twelve) : d1276 (change pattern 1 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 1 12) else d9 (change pattern 1 12)) = d1276 pattern
  rw [s5563, s5475]
  rfl
theorem s5620 (pattern : Twelve) : d1279 (change pattern 1 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 1 12) else d1275 (change pattern 1 12)) = d1279 pattern
  rw [s5619, s5613]
  rfl
theorem s5621 (pattern : Twelve) : d1280 (change pattern 1 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d872 (change pattern 1 12)) = d1280 pattern
  rw [s5467, s5545]
  rfl
theorem s5622 (pattern : Twelve) : d1285 (change pattern 1 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 1 12) else d1279 (change pattern 1 12)) = d1285 pattern
  rw [s5621, s5620]
  rfl
theorem s5623 (pattern : Twelve) : d1295 (change pattern 1 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 1 12) else d827 (change pattern 1 12)) = d1295 pattern
  rw [s5622, s5482]
  rfl
theorem s5624 (pattern : Twelve) : d29 (change pattern 1 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d19 (change pattern 1 12)) = d29 pattern
  rw [s5467, s5460]
  rfl
theorem s5625 (pattern : Twelve) : d1286 (change pattern 1 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 1 12) else d817 (change pattern 1 12)) = d1286 pattern
  rw [s5624, s5466]
  rfl
theorem s5626 (pattern : Twelve) : d1296 (change pattern 1 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1286 (change pattern 1 12)) = d1296 pattern
  rw [s5467, s5625]
  rfl
theorem s5627 (pattern : Twelve) : d1306 (change pattern 1 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 1 12) else d1295 (change pattern 1 12)) = d1306 pattern
  rw [s5626, s5623]
  rfl
theorem s5628 (pattern : Twelve) : d1313 (change pattern 1 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 1 12) else d1305 (change pattern 1 12)) = d1313 pattern
  rw [s5627, s5618]
  rfl
theorem s5629 (pattern : Twelve) : d1281 (change pattern 1 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 1 12) else d872 (change pattern 1 12)) = d1281 pattern
  rw [s5564, s5545]
  rfl
theorem s5630 (pattern : Twelve) : d1287 (change pattern 1 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 1 12) else d1279 (change pattern 1 12)) = d1287 pattern
  rw [s5629, s5620]
  rfl
theorem s5631 (pattern : Twelve) : d1297 (change pattern 1 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 1 12) else d34 (change pattern 1 12)) = d1297 pattern
  rw [s5630, s5477]
  rfl
theorem s5632 (pattern : Twelve) : d1298 (change pattern 1 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d817 (change pattern 1 12)) = d1298 pattern
  rw [s5467, s5466]
  rfl
theorem s5633 (pattern : Twelve) : d1307 (change pattern 1 12) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 1 12) else d1297 (change pattern 1 12)) = d1307 pattern
  rw [s5632, s5631]
  rfl
theorem s5634 (pattern : Twelve) : d1277 (change pattern 1 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 1 12) else d15 (change pattern 1 12)) = d1277 pattern
  rw [s5504, s5494]
  rfl
theorem s5635 (pattern : Twelve) : d1282 (change pattern 1 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 1 12) else d1276 (change pattern 1 12)) = d1282 pattern
  rw [s5634, s5619]
  rfl
theorem s5636 (pattern : Twelve) : d1288 (change pattern 1 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 1 12) else d1282 (change pattern 1 12)) = d1288 pattern
  rw [s5577, s5635]
  rfl
theorem s5637 (pattern : Twelve) : d1299 (change pattern 1 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 1 12) else d830 (change pattern 1 12)) = d1299 pattern
  rw [s5636, s5502]
  rfl
theorem s5638 (pattern : Twelve) : d1289 (change pattern 1 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 1 12) else d821 (change pattern 1 12)) = d1289 pattern
  rw [s5468, s5506]
  rfl
theorem s5639 (pattern : Twelve) : d1300 (change pattern 1 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1289 (change pattern 1 12)) = d1300 pattern
  rw [s5467, s5638]
  rfl
theorem s5640 (pattern : Twelve) : d1308 (change pattern 1 12) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 1 12) else d1299 (change pattern 1 12)) = d1308 pattern
  rw [s5639, s5637]
  rfl
theorem s5641 (pattern : Twelve) : d1314 (change pattern 1 12) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 1 12) else d1307 (change pattern 1 12)) = d1314 pattern
  rw [s5640, s5633]
  rfl
theorem s5642 (pattern : Twelve) : d1315 (change pattern 1 12) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1306 (change pattern 1 12)) = d1315 pattern
  rw [s5467, s5627]
  rfl
theorem s5643 (pattern : Twelve) : d1319 (change pattern 1 12) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 1 12) else d1314 (change pattern 1 12)) = d1319 pattern
  rw [s5642, s5641]
  rfl
theorem s5644 (pattern : Twelve) : d1321 (change pattern 1 12) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 1 12) else d1313 (change pattern 1 12)) = d1321 pattern
  rw [s5643, s5628]
  rfl
theorem s5645 (pattern : Twelve) : d1283 (change pattern 1 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 1 12) else d19 (change pattern 1 12)) = d1283 pattern
  rw [s5476, s5460]
  rfl
theorem s5646 (pattern : Twelve) : d1301 (change pattern 1 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1283 (change pattern 1 12)) = d1301 pattern
  rw [s5467, s5645]
  rfl
theorem s5647 (pattern : Twelve) : d1309 (change pattern 1 12) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 1 12) else d1293 (change pattern 1 12)) = d1309 pattern
  rw [s5646, s5616]
  rfl
theorem s5648 (pattern : Twelve) : d1290 (change pattern 1 12) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 1 12) else d817 (change pattern 1 12)) = d1290 pattern
  rw [s5501, s5466]
  rfl
theorem s5649 (pattern : Twelve) : d1302 (change pattern 1 12) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1290 (change pattern 1 12)) = d1302 pattern
  rw [s5467, s5648]
  rfl
theorem s5650 (pattern : Twelve) : d1310 (change pattern 1 12) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 1 12) else d1295 (change pattern 1 12)) = d1310 pattern
  rw [s5649, s5623]
  rfl
theorem s5651 (pattern : Twelve) : d1316 (change pattern 1 12) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 1 12) else d1309 (change pattern 1 12)) = d1316 pattern
  rw [s5650, s5647]
  rfl
theorem s5652 (pattern : Twelve) : d1291 (change pattern 1 12) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 1 12) else d817 (change pattern 1 12)) = d1291 pattern
  rw [s5496, s5466]
  rfl
theorem s5653 (pattern : Twelve) : d1303 (change pattern 1 12) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1291 (change pattern 1 12)) = d1303 pattern
  rw [s5467, s5652]
  rfl
theorem s5654 (pattern : Twelve) : d1311 (change pattern 1 12) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 1 12) else d1297 (change pattern 1 12)) = d1311 pattern
  rw [s5653, s5631]
  rfl
theorem s5655 (pattern : Twelve) : d1292 (change pattern 1 12) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 1 12) else d821 (change pattern 1 12)) = d1292 pattern
  rw [s5598, s5506]
  rfl
theorem s5656 (pattern : Twelve) : d1304 (change pattern 1 12) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1292 (change pattern 1 12)) = d1304 pattern
  rw [s5467, s5655]
  rfl
theorem s5657 (pattern : Twelve) : d1312 (change pattern 1 12) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 1 12) else d1299 (change pattern 1 12)) = d1312 pattern
  rw [s5656, s5637]
  rfl
theorem s5658 (pattern : Twelve) : d1317 (change pattern 1 12) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 1 12) else d1311 (change pattern 1 12)) = d1317 pattern
  rw [s5657, s5654]
  rfl
theorem s5659 (pattern : Twelve) : d1318 (change pattern 1 12) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1310 (change pattern 1 12)) = d1318 pattern
  rw [s5467, s5650]
  rfl
theorem s5660 (pattern : Twelve) : d1320 (change pattern 1 12) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 1 12) else d1317 (change pattern 1 12)) = d1320 pattern
  rw [s5659, s5658]
  rfl
theorem s5661 (pattern : Twelve) : d1322 (change pattern 1 12) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 1 12) else d1316 (change pattern 1 12)) = d1322 pattern
  rw [s5660, s5651]
  rfl
theorem s5662 (pattern : Twelve) : d1323 (change pattern 1 12) = d1323 pattern := by
  change (if pattern.g then d1322 (change pattern 1 12) else d1321 (change pattern 1 12)) = d1323 pattern
  rw [s5661, s5644]
  rfl
theorem s5663 (pattern : Twelve) : d1640 (change pattern 1 12) = d1323 pattern := by
  change d1323 (change pattern 1 12) = d1323 pattern
  exact s5662 pattern
theorem s5664 (pattern : Twelve) : d1324 (change pattern 1 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 1 12) else d11 (change pattern 1 12)) = d1324 pattern
  rw [s5462, s5459]
  rfl
theorem s5665 (pattern : Twelve) : d1325 (change pattern 1 12) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 1 12) else d1275 (change pattern 1 12)) = d1325 pattern
  rw [s5664, s5613]
  rfl
theorem s5666 (pattern : Twelve) : d1326 (change pattern 1 12) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 1 12) else d872 (change pattern 1 12)) = d1326 pattern
  rw [s5664, s5545]
  rfl
theorem s5667 (pattern : Twelve) : d1333 (change pattern 1 12) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 1 12) else d1325 (change pattern 1 12)) = d1333 pattern
  rw [s5666, s5665]
  rfl
theorem s5668 (pattern : Twelve) : d1339 (change pattern 1 12) = d1339 pattern := by
  change (if pattern.f then d1333 (change pattern 1 12) else d17 (change pattern 1 12)) = d1339 pattern
  rw [s5667, s5450]
  rfl
theorem s5669 (pattern : Twelve) : d1345 (change pattern 1 12) = d1345 pattern := by
  change (if pattern.e then d1294 (change pattern 1 12) else d1339 (change pattern 1 12)) = d1345 pattern
  rw [s5617, s5668]
  rfl
theorem s5670 (pattern : Twelve) : d1327 (change pattern 1 12) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 1 12) else d1275 (change pattern 1 12)) = d1327 pattern
  rw [s5564, s5613]
  rfl
theorem s5671 (pattern : Twelve) : d1334 (change pattern 1 12) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 1 12) else d1327 (change pattern 1 12)) = d1334 pattern
  rw [s5621, s5670]
  rfl
theorem s5672 (pattern : Twelve) : d1340 (change pattern 1 12) = d1340 pattern := by
  change (if pattern.f then d1334 (change pattern 1 12) else d827 (change pattern 1 12)) = d1340 pattern
  rw [s5671, s5482]
  rfl
theorem s5673 (pattern : Twelve) : d1346 (change pattern 1 12) = d1346 pattern := by
  change (if pattern.e then d1296 (change pattern 1 12) else d1340 (change pattern 1 12)) = d1346 pattern
  rw [s5626, s5672]
  rfl
theorem s5674 (pattern : Twelve) : d1349 (change pattern 1 12) = d1349 pattern := by
  change (if pattern.j then d1346 (change pattern 1 12) else d1345 (change pattern 1 12)) = d1349 pattern
  rw [s5673, s5669]
  rfl
theorem s5675 (pattern : Twelve) : d1328 (change pattern 1 12) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 1 12) else d872 (change pattern 1 12)) = d1328 pattern
  rw [s5634, s5545]
  rfl
theorem s5676 (pattern : Twelve) : d1335 (change pattern 1 12) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 1 12) else d1327 (change pattern 1 12)) = d1335 pattern
  rw [s5675, s5670]
  rfl
theorem s5677 (pattern : Twelve) : d1341 (change pattern 1 12) = d1341 pattern := by
  change (if pattern.f then d1335 (change pattern 1 12) else d34 (change pattern 1 12)) = d1341 pattern
  rw [s5676, s5477]
  rfl
theorem s5678 (pattern : Twelve) : d20 (change pattern 1 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 1 12) else d12 (change pattern 1 12)) = d20 pattern
  rw [s5503, s5464]
  rfl
theorem s5679 (pattern : Twelve) : d1329 (change pattern 1 12) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 1 12) else d19 (change pattern 1 12)) = d1329 pattern
  rw [s5678, s5460]
  rfl
theorem s5680 (pattern : Twelve) : d1336 (change pattern 1 12) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 1 12) else d817 (change pattern 1 12)) = d1336 pattern
  rw [s5679, s5466]
  rfl
theorem s5681 (pattern : Twelve) : d1342 (change pattern 1 12) = d1342 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1336 (change pattern 1 12)) = d1342 pattern
  rw [s5467, s5680]
  rfl
theorem s5682 (pattern : Twelve) : d1347 (change pattern 1 12) = d1347 pattern := by
  change (if pattern.e then d1342 (change pattern 1 12) else d1341 (change pattern 1 12)) = d1347 pattern
  rw [s5681, s5677]
  rfl
theorem s5683 (pattern : Twelve) : d1330 (change pattern 1 12) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d1276 (change pattern 1 12)) = d1330 pattern
  rw [s5467, s5619]
  rfl
theorem s5684 (pattern : Twelve) : d1331 (change pattern 1 12) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d1277 (change pattern 1 12)) = d1331 pattern
  rw [s5467, s5634]
  rfl
theorem s5685 (pattern : Twelve) : d1337 (change pattern 1 12) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 1 12) else d1330 (change pattern 1 12)) = d1337 pattern
  rw [s5684, s5683]
  rfl
theorem s5686 (pattern : Twelve) : d1343 (change pattern 1 12) = d1343 pattern := by
  change (if pattern.f then d1337 (change pattern 1 12) else d830 (change pattern 1 12)) = d1343 pattern
  rw [s5685, s5502]
  rfl
theorem s5687 (pattern : Twelve) : d1332 (change pattern 1 12) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d25 (change pattern 1 12)) = d1332 pattern
  rw [s5569, s5465]
  rfl
theorem s5688 (pattern : Twelve) : d128 (change pattern 1 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d20 (change pattern 1 12)) = d128 pattern
  rw [s5467, s5678]
  rfl
theorem s5689 (pattern : Twelve) : d1338 (change pattern 1 12) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 1 12) else d1332 (change pattern 1 12)) = d1338 pattern
  rw [s5688, s5687]
  rfl
theorem s5690 (pattern : Twelve) : d1344 (change pattern 1 12) = d1344 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1338 (change pattern 1 12)) = d1344 pattern
  rw [s5467, s5689]
  rfl
theorem s5691 (pattern : Twelve) : d1348 (change pattern 1 12) = d1348 pattern := by
  change (if pattern.e then d1344 (change pattern 1 12) else d1343 (change pattern 1 12)) = d1348 pattern
  rw [s5690, s5686]
  rfl
theorem s5692 (pattern : Twelve) : d1350 (change pattern 1 12) = d1350 pattern := by
  change (if pattern.j then d1348 (change pattern 1 12) else d1347 (change pattern 1 12)) = d1350 pattern
  rw [s5691, s5682]
  rfl
theorem s5693 (pattern : Twelve) : d1351 (change pattern 1 12) = d1351 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1346 (change pattern 1 12)) = d1351 pattern
  rw [s5467, s5673]
  rfl
theorem s5694 (pattern : Twelve) : d1352 (change pattern 1 12) = d1352 pattern := by
  change (if pattern.d then d1351 (change pattern 1 12) else d1350 (change pattern 1 12)) = d1352 pattern
  rw [s5693, s5692]
  rfl
theorem s5695 (pattern : Twelve) : d1353 (change pattern 1 12) = d1353 pattern := by
  change (if pattern.c then d1352 (change pattern 1 12) else d1349 (change pattern 1 12)) = d1353 pattern
  rw [s5694, s5674]
  rfl
theorem s5696 (pattern : Twelve) : d1616 (change pattern 1 12) = d1616 pattern := by
  change (if pattern.i then d119 (change pattern 1 12) else d1276 (change pattern 1 12)) = d1616 pattern
  rw [s5564, s5619]
  rfl
theorem s5697 (pattern : Twelve) : d1619 (change pattern 1 12) = d1619 pattern := by
  change (if pattern.h then d119 (change pattern 1 12) else d1616 (change pattern 1 12)) = d1619 pattern
  rw [s5564, s5696]
  rfl
theorem s5698 (pattern : Twelve) : d1622 (change pattern 1 12) = d1622 pattern := by
  change (if pattern.f then d1619 (change pattern 1 12) else d23 (change pattern 1 12)) = d1622 pattern
  rw [s5697, s5476]
  rfl
theorem s5699 (pattern : Twelve) : d1617 (change pattern 1 12) = d1617 pattern := by
  change (if pattern.i then d24 (change pattern 1 12) else d25 (change pattern 1 12)) = d1617 pattern
  rw [s5495, s5465]
  rfl
end NetHack.Sokoban21.Diagram
