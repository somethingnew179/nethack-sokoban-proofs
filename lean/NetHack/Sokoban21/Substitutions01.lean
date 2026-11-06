/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions00
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s150 (pattern : Twelve) : d1322 (change pattern 12 12) = d1322 pattern := by
  change (if pattern.c then d1320 (change pattern 12 12) else d1316 (change pattern 12 12)) = d1322 pattern
  rw [s149, s139]
  rfl
theorem s151 (pattern : Twelve) : d1323 (change pattern 12 12) = d1323 pattern := by
  change (if pattern.g then d1322 (change pattern 12 12) else d1321 (change pattern 12 12)) = d1323 pattern
  rw [s150, s132]
  rfl
theorem s152 (pattern : Twelve) : d1324 (change pattern 12 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 12) else d11 (change pattern 12 12)) = d1324 pattern
  rw [s15, s12]
  rfl
theorem s153 (pattern : Twelve) : d1649 (change pattern 12 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 12) else d19 (change pattern 12 12)) = d1649 pattern
  rw [s152, s13]
  rfl
theorem s154 (pattern : Twelve) : d1650 (change pattern 12 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d25 (change pattern 12 12)) = d1650 pattern
  rw [s20, s18]
  rfl
theorem s155 (pattern : Twelve) : d1656 (change pattern 12 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 12) else d1649 (change pattern 12 12)) = d1656 pattern
  rw [s154, s153]
  rfl
theorem s156 (pattern : Twelve) : d20 (change pattern 12 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 12) else d12 (change pattern 12 12)) = d20 pattern
  rw [s56, s17]
  rfl
theorem s157 (pattern : Twelve) : d1644 (change pattern 12 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 12) else d1324 (change pattern 12 12)) = d1644 pattern
  rw [s156, s152]
  rfl
theorem s158 (pattern : Twelve) : d1645 (change pattern 12 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d1324 (change pattern 12 12)) = d1645 pattern
  rw [s20, s152]
  rfl
theorem s159 (pattern : Twelve) : d1647 (change pattern 12 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 12) else d1644 (change pattern 12 12)) = d1647 pattern
  rw [s158, s157]
  rfl
theorem s160 (pattern : Twelve) : d1651 (change pattern 12 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 12 12) else d1286 (change pattern 12 12)) = d1651 pattern
  rw [s159, s111]
  rfl
theorem s161 (pattern : Twelve) : d1657 (change pattern 12 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 12 12) else d1651 (change pattern 12 12)) = d1657 pattern
  rw [s127, s160]
  rfl
theorem s162 (pattern : Twelve) : d1660 (change pattern 12 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 12 12) else d1656 (change pattern 12 12)) = d1660 pattern
  rw [s161, s155]
  rfl
theorem s163 (pattern : Twelve) : d1652 (change pattern 12 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 12 12) else d817 (change pattern 12 12)) = d1652 pattern
  rw [s157, s19]
  rfl
theorem s164 (pattern : Twelve) : d1653 (change pattern 12 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d821 (change pattern 12 12)) = d1653 pattern
  rw [s20, s59]
  rfl
theorem s165 (pattern : Twelve) : d1658 (change pattern 12 12) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 12 12) else d1652 (change pattern 12 12)) = d1658 pattern
  rw [s164, s163]
  rfl
theorem s166 (pattern : Twelve) : d22 (change pattern 12 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d14 (change pattern 12 12)) = d22 pattern
  rw [s20, s57]
  rfl
theorem s167 (pattern : Twelve) : d1646 (change pattern 12 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d20 (change pattern 12 12)) = d1646 pattern
  rw [s166, s156]
  rfl
theorem s168 (pattern : Twelve) : d128 (change pattern 12 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d20 (change pattern 12 12)) = d128 pattern
  rw [s20, s156]
  rfl
theorem s169 (pattern : Twelve) : d1648 (change pattern 12 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 12 12) else d1646 (change pattern 12 12)) = d1648 pattern
  rw [s168, s167]
  rfl
theorem s170 (pattern : Twelve) : d1654 (change pattern 12 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 12 12) else d1289 (change pattern 12 12)) = d1654 pattern
  rw [s169, s126]
  rfl
theorem s171 (pattern : Twelve) : d1655 (change pattern 12 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d822 (change pattern 12 12)) = d1655 pattern
  rw [s20, s60]
  rfl
theorem s172 (pattern : Twelve) : d1659 (change pattern 12 12) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 12 12) else d1654 (change pattern 12 12)) = d1659 pattern
  rw [s171, s170]
  rfl
theorem s173 (pattern : Twelve) : d1661 (change pattern 12 12) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 12 12) else d1658 (change pattern 12 12)) = d1661 pattern
  rw [s172, s165]
  rfl
theorem s174 (pattern : Twelve) : d1662 (change pattern 12 12) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1657 (change pattern 12 12)) = d1662 pattern
  rw [s20, s161]
  rfl
theorem s175 (pattern : Twelve) : d1663 (change pattern 12 12) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 12 12) else d1661 (change pattern 12 12)) = d1663 pattern
  rw [s174, s173]
  rfl
theorem s176 (pattern : Twelve) : d1664 (change pattern 12 12) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 12 12) else d1660 (change pattern 12 12)) = d1664 pattern
  rw [s175, s162]
  rfl
theorem s177 (pattern : Twelve) : d874 (change pattern 12 12) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 12 12) else d17 (change pattern 12 12)) = d874 pattern
  rw [s98, s3]
  rfl
theorem s178 (pattern : Twelve) : d875 (change pattern 12 12) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 12 12) else d814 (change pattern 12 12)) = d875 pattern
  rw [s98, s5]
  rfl
theorem s179 (pattern : Twelve) : d882 (change pattern 12 12) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 12 12) else d874 (change pattern 12 12)) = d882 pattern
  rw [s178, s177]
  rfl
theorem s180 (pattern : Twelve) : d890 (change pattern 12 12) = d890 pattern := by
  change (if pattern.f then d882 (change pattern 12 12) else d0 (change pattern 12 12)) = d890 pattern
  rw [s179, s0]
  rfl
theorem s181 (pattern : Twelve) : d876 (change pattern 12 12) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 12 12) else d19 (change pattern 12 12)) = d876 pattern
  rw [s58, s13]
  rfl
theorem s182 (pattern : Twelve) : d883 (change pattern 12 12) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 12 12) else d876 (change pattern 12 12)) = d883 pattern
  rw [s21, s181]
  rfl
theorem s183 (pattern : Twelve) : d891 (change pattern 12 12) = d891 pattern := by
  change (if pattern.f then d883 (change pattern 12 12) else d17 (change pattern 12 12)) = d891 pattern
  rw [s182, s3]
  rfl
theorem s184 (pattern : Twelve) : d898 (change pattern 12 12) = d898 pattern := by
  change (if pattern.e then d891 (change pattern 12 12) else d890 (change pattern 12 12)) = d898 pattern
  rw [s183, s180]
  rfl
theorem s185 (pattern : Twelve) : d877 (change pattern 12 12) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 12 12) else d17 (change pattern 12 12)) = d877 pattern
  rw [s50, s3]
  rfl
theorem s186 (pattern : Twelve) : d884 (change pattern 12 12) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 12 12) else d877 (change pattern 12 12)) = d884 pattern
  rw [s31, s185]
  rfl
theorem s187 (pattern : Twelve) : d892 (change pattern 12 12) = d892 pattern := by
  change (if pattern.f then d884 (change pattern 12 12) else d56 (change pattern 12 12)) = d892 pattern
  rw [s186, s27]
  rfl
theorem s188 (pattern : Twelve) : d893 (change pattern 12 12) = d893 pattern := by
  change (if pattern.f then d883 (change pattern 12 12) else d827 (change pattern 12 12)) = d893 pattern
  rw [s182, s35]
  rfl
theorem s189 (pattern : Twelve) : d899 (change pattern 12 12) = d899 pattern := by
  change (if pattern.e then d893 (change pattern 12 12) else d892 (change pattern 12 12)) = d899 pattern
  rw [s188, s187]
  rfl
theorem s190 (pattern : Twelve) : d902 (change pattern 12 12) = d902 pattern := by
  change (if pattern.j then d899 (change pattern 12 12) else d898 (change pattern 12 12)) = d902 pattern
  rw [s189, s184]
  rfl
theorem s191 (pattern : Twelve) : d878 (change pattern 12 12) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 12 12) else d814 (change pattern 12 12)) = d878 pattern
  rw [s48, s5]
  rfl
theorem s192 (pattern : Twelve) : d885 (change pattern 12 12) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 12 12) else d877 (change pattern 12 12)) = d885 pattern
  rw [s191, s185]
  rfl
theorem s193 (pattern : Twelve) : d894 (change pattern 12 12) = d894 pattern := by
  change (if pattern.f then d885 (change pattern 12 12) else d30 (change pattern 12 12)) = d894 pattern
  rw [s192, s25]
  rfl
theorem s194 (pattern : Twelve) : d879 (change pattern 12 12) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 12 12) else d17 (change pattern 12 12)) = d879 pattern
  rw [s115, s3]
  rfl
theorem s195 (pattern : Twelve) : d886 (change pattern 12 12) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 12 12) else d34 (change pattern 12 12)) = d886 pattern
  rw [s194, s30]
  rfl
theorem s196 (pattern : Twelve) : d895 (change pattern 12 12) = d895 pattern := by
  change (if pattern.f then d883 (change pattern 12 12) else d886 (change pattern 12 12)) = d895 pattern
  rw [s182, s195]
  rfl
theorem s197 (pattern : Twelve) : d900 (change pattern 12 12) = d900 pattern := by
  change (if pattern.e then d895 (change pattern 12 12) else d894 (change pattern 12 12)) = d900 pattern
  rw [s196, s193]
  rfl
theorem s198 (pattern : Twelve) : d127 (change pattern 12 12) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d23 (change pattern 12 12)) = d127 pattern
  rw [s166, s29]
  rfl
theorem s199 (pattern : Twelve) : d873 (change pattern 12 12) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 12 12) else d117 (change pattern 12 12)) = d873 pattern
  rw [s47, s104]
  rfl
theorem s200 (pattern : Twelve) : d880 (change pattern 12 12) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d873 (change pattern 12 12)) = d880 pattern
  rw [s20, s199]
  rfl
theorem s201 (pattern : Twelve) : d887 (change pattern 12 12) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 12 12) else d127 (change pattern 12 12)) = d887 pattern
  rw [s200, s198]
  rfl
theorem s202 (pattern : Twelve) : d896 (change pattern 12 12) = d896 pattern := by
  change (if pattern.f then d887 (change pattern 12 12) else d59 (change pattern 12 12)) = d896 pattern
  rw [s201, s46]
  rfl
theorem s203 (pattern : Twelve) : d118 (change pattern 12 12) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 12) else d5 (change pattern 12 12)) = d118 pattern
  rw [s57, s16]
  rfl
theorem s204 (pattern : Twelve) : d881 (change pattern 12 12) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 12 12) else d23 (change pattern 12 12)) = d881 pattern
  rw [s203, s29]
  rfl
theorem s205 (pattern : Twelve) : d888 (change pattern 12 12) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 12 12) else d881 (change pattern 12 12)) = d888 pattern
  rw [s123, s204]
  rfl
theorem s206 (pattern : Twelve) : d889 (change pattern 12 12) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d42 (change pattern 12 12)) = d889 pattern
  rw [s20, s21]
  rfl
theorem s207 (pattern : Twelve) : d897 (change pattern 12 12) = d897 pattern := by
  change (if pattern.f then d889 (change pattern 12 12) else d888 (change pattern 12 12)) = d897 pattern
  rw [s206, s205]
  rfl
theorem s208 (pattern : Twelve) : d901 (change pattern 12 12) = d901 pattern := by
  change (if pattern.e then d897 (change pattern 12 12) else d896 (change pattern 12 12)) = d901 pattern
  rw [s207, s202]
  rfl
theorem s209 (pattern : Twelve) : d903 (change pattern 12 12) = d903 pattern := by
  change (if pattern.j then d901 (change pattern 12 12) else d900 (change pattern 12 12)) = d903 pattern
  rw [s208, s197]
  rfl
theorem s210 (pattern : Twelve) : d904 (change pattern 12 12) = d904 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d899 (change pattern 12 12)) = d904 pattern
  rw [s20, s189]
  rfl
theorem s211 (pattern : Twelve) : d905 (change pattern 12 12) = d905 pattern := by
  change (if pattern.d then d904 (change pattern 12 12) else d903 (change pattern 12 12)) = d905 pattern
  rw [s210, s209]
  rfl
theorem s212 (pattern : Twelve) : d906 (change pattern 12 12) = d906 pattern := by
  change (if pattern.c then d905 (change pattern 12 12) else d902 (change pattern 12 12)) = d906 pattern
  rw [s211, s190]
  rfl
theorem s213 (pattern : Twelve) : d907 (change pattern 12 12) = d907 pattern := by
  change (if pattern.a then d906 (change pattern 12 12) else d869 (change pattern 12 12)) = d907 pattern
  rw [s212, s67]
  rfl
theorem s214 (pattern : Twelve) : d1325 (change pattern 12 12) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 12 12) else d1275 (change pattern 12 12)) = d1325 pattern
  rw [s152, s97]
  rfl
theorem s215 (pattern : Twelve) : d1326 (change pattern 12 12) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 12 12) else d872 (change pattern 12 12)) = d1326 pattern
  rw [s152, s98]
  rfl
theorem s216 (pattern : Twelve) : d1333 (change pattern 12 12) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 12 12) else d1325 (change pattern 12 12)) = d1333 pattern
  rw [s215, s214]
  rfl
theorem s217 (pattern : Twelve) : d1339 (change pattern 12 12) = d1339 pattern := by
  change (if pattern.f then d1333 (change pattern 12 12) else d17 (change pattern 12 12)) = d1339 pattern
  rw [s216, s3]
  rfl
theorem s218 (pattern : Twelve) : d1345 (change pattern 12 12) = d1345 pattern := by
  change (if pattern.e then d1294 (change pattern 12 12) else d1339 (change pattern 12 12)) = d1345 pattern
  rw [s102, s217]
  rfl
theorem s219 (pattern : Twelve) : d1327 (change pattern 12 12) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 12 12) else d1275 (change pattern 12 12)) = d1327 pattern
  rw [s115, s97]
  rfl
theorem s220 (pattern : Twelve) : d1334 (change pattern 12 12) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 12 12) else d1327 (change pattern 12 12)) = d1334 pattern
  rw [s107, s219]
  rfl
theorem s221 (pattern : Twelve) : d1340 (change pattern 12 12) = d1340 pattern := by
  change (if pattern.f then d1334 (change pattern 12 12) else d827 (change pattern 12 12)) = d1340 pattern
  rw [s220, s35]
  rfl
theorem s222 (pattern : Twelve) : d1346 (change pattern 12 12) = d1346 pattern := by
  change (if pattern.e then d1296 (change pattern 12 12) else d1340 (change pattern 12 12)) = d1346 pattern
  rw [s112, s221]
  rfl
theorem s223 (pattern : Twelve) : d1349 (change pattern 12 12) = d1349 pattern := by
  change (if pattern.j then d1346 (change pattern 12 12) else d1345 (change pattern 12 12)) = d1349 pattern
  rw [s222, s218]
  rfl
theorem s224 (pattern : Twelve) : d1328 (change pattern 12 12) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 12 12) else d872 (change pattern 12 12)) = d1328 pattern
  rw [s121, s98]
  rfl
theorem s225 (pattern : Twelve) : d1335 (change pattern 12 12) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 12 12) else d1327 (change pattern 12 12)) = d1335 pattern
  rw [s224, s219]
  rfl
theorem s226 (pattern : Twelve) : d1341 (change pattern 12 12) = d1341 pattern := by
  change (if pattern.f then d1335 (change pattern 12 12) else d34 (change pattern 12 12)) = d1341 pattern
  rw [s225, s30]
  rfl
theorem s227 (pattern : Twelve) : d1329 (change pattern 12 12) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 12 12) else d19 (change pattern 12 12)) = d1329 pattern
  rw [s156, s13]
  rfl
theorem s228 (pattern : Twelve) : d1336 (change pattern 12 12) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 12 12) else d817 (change pattern 12 12)) = d1336 pattern
  rw [s227, s19]
  rfl
theorem s229 (pattern : Twelve) : d1342 (change pattern 12 12) = d1342 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1336 (change pattern 12 12)) = d1342 pattern
  rw [s20, s228]
  rfl
theorem s230 (pattern : Twelve) : d1347 (change pattern 12 12) = d1347 pattern := by
  change (if pattern.e then d1342 (change pattern 12 12) else d1341 (change pattern 12 12)) = d1347 pattern
  rw [s229, s226]
  rfl
theorem s231 (pattern : Twelve) : d1330 (change pattern 12 12) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d1276 (change pattern 12 12)) = d1330 pattern
  rw [s20, s105]
  rfl
theorem s232 (pattern : Twelve) : d1331 (change pattern 12 12) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d1277 (change pattern 12 12)) = d1331 pattern
  rw [s20, s121]
  rfl
theorem s233 (pattern : Twelve) : d1337 (change pattern 12 12) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 12 12) else d1330 (change pattern 12 12)) = d1337 pattern
  rw [s232, s231]
  rfl
theorem s234 (pattern : Twelve) : d1343 (change pattern 12 12) = d1343 pattern := by
  change (if pattern.f then d1337 (change pattern 12 12) else d830 (change pattern 12 12)) = d1343 pattern
  rw [s233, s55]
  rfl
theorem s235 (pattern : Twelve) : d1332 (change pattern 12 12) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d25 (change pattern 12 12)) = d1332 pattern
  rw [s166, s18]
  rfl
theorem s236 (pattern : Twelve) : d1338 (change pattern 12 12) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 12 12) else d1332 (change pattern 12 12)) = d1338 pattern
  rw [s168, s235]
  rfl
theorem s237 (pattern : Twelve) : d1344 (change pattern 12 12) = d1344 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1338 (change pattern 12 12)) = d1344 pattern
  rw [s20, s236]
  rfl
theorem s238 (pattern : Twelve) : d1348 (change pattern 12 12) = d1348 pattern := by
  change (if pattern.e then d1344 (change pattern 12 12) else d1343 (change pattern 12 12)) = d1348 pattern
  rw [s237, s234]
  rfl
theorem s239 (pattern : Twelve) : d1350 (change pattern 12 12) = d1350 pattern := by
  change (if pattern.j then d1348 (change pattern 12 12) else d1347 (change pattern 12 12)) = d1350 pattern
  rw [s238, s230]
  rfl
theorem s240 (pattern : Twelve) : d1351 (change pattern 12 12) = d1351 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1346 (change pattern 12 12)) = d1351 pattern
  rw [s20, s222]
  rfl
theorem s241 (pattern : Twelve) : d1352 (change pattern 12 12) = d1352 pattern := by
  change (if pattern.d then d1351 (change pattern 12 12) else d1350 (change pattern 12 12)) = d1352 pattern
  rw [s240, s239]
  rfl
theorem s242 (pattern : Twelve) : d1353 (change pattern 12 12) = d1353 pattern := by
  change (if pattern.c then d1352 (change pattern 12 12) else d1349 (change pattern 12 12)) = d1353 pattern
  rw [s241, s223]
  rfl
theorem s243 (pattern : Twelve) : d1354 (change pattern 12 12) = d1354 pattern := by
  change (if pattern.a then d1353 (change pattern 12 12) else d1321 (change pattern 12 12)) = d1354 pattern
  rw [s242, s132]
  rfl
theorem s244 (pattern : Twelve) : d1668 (change pattern 12 12) = d1668 pattern := by
  change (if pattern.f then d1644 (change pattern 12 12) else d19 (change pattern 12 12)) = d1668 pattern
  rw [s157, s13]
  rfl
theorem s245 (pattern : Twelve) : d1671 (change pattern 12 12) = d1671 pattern := by
  change (if pattern.e then d1650 (change pattern 12 12) else d1668 (change pattern 12 12)) = d1671 pattern
  rw [s154, s244]
  rfl
theorem s246 (pattern : Twelve) : d1674 (change pattern 12 12) = d1674 pattern := by
  change (if pattern.j then d1657 (change pattern 12 12) else d1671 (change pattern 12 12)) = d1674 pattern
  rw [s161, s245]
  rfl
theorem s247 (pattern : Twelve) : d1665 (change pattern 12 12) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d1324 (change pattern 12 12)) = d1665 pattern
  rw [s166, s152]
  rfl
theorem s248 (pattern : Twelve) : d1666 (change pattern 12 12) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 12 12) else d1644 (change pattern 12 12)) = d1666 pattern
  rw [s247, s157]
  rfl
theorem s249 (pattern : Twelve) : d1669 (change pattern 12 12) = d1669 pattern := by
  change (if pattern.f then d1666 (change pattern 12 12) else d817 (change pattern 12 12)) = d1669 pattern
  rw [s248, s19]
  rfl
theorem s250 (pattern : Twelve) : d1672 (change pattern 12 12) = d1672 pattern := by
  change (if pattern.e then d1300 (change pattern 12 12) else d1669 (change pattern 12 12)) = d1672 pattern
  rw [s127, s249]
  rfl
theorem s251 (pattern : Twelve) : d183 (change pattern 12 12) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d22 (change pattern 12 12)) = d183 pattern
  rw [s20, s166]
  rfl
theorem s252 (pattern : Twelve) : d1667 (change pattern 12 12) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 12 12) else d128 (change pattern 12 12)) = d1667 pattern
  rw [s251, s168]
  rfl
theorem s253 (pattern : Twelve) : d1670 (change pattern 12 12) = d1670 pattern := by
  change (if pattern.f then d1667 (change pattern 12 12) else d1289 (change pattern 12 12)) = d1670 pattern
  rw [s252, s126]
  rfl
theorem s254 (pattern : Twelve) : d1252 (change pattern 12 12) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d822 (change pattern 12 12)) = d1252 pattern
  rw [s20, s60]
  rfl
theorem s255 (pattern : Twelve) : d1626 (change pattern 12 12) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1252 (change pattern 12 12)) = d1626 pattern
  rw [s20, s254]
  rfl
theorem s256 (pattern : Twelve) : d1673 (change pattern 12 12) = d1673 pattern := by
  change (if pattern.e then d1626 (change pattern 12 12) else d1670 (change pattern 12 12)) = d1673 pattern
  rw [s255, s253]
  rfl
theorem s257 (pattern : Twelve) : d1675 (change pattern 12 12) = d1675 pattern := by
  change (if pattern.j then d1673 (change pattern 12 12) else d1672 (change pattern 12 12)) = d1675 pattern
  rw [s256, s250]
  rfl
theorem s258 (pattern : Twelve) : d1676 (change pattern 12 12) = d1676 pattern := by
  change (if pattern.d then d1662 (change pattern 12 12) else d1675 (change pattern 12 12)) = d1676 pattern
  rw [s174, s257]
  rfl
theorem s259 (pattern : Twelve) : d1677 (change pattern 12 12) = d1677 pattern := by
  change (if pattern.c then d1676 (change pattern 12 12) else d1674 (change pattern 12 12)) = d1677 pattern
  rw [s258, s246]
  rfl
theorem s260 (pattern : Twelve) : d1678 (change pattern 12 12) = d1678 pattern := by
  change (if pattern.a then d1677 (change pattern 12 12) else d1664 (change pattern 12 12)) = d1678 pattern
  rw [s259, s176]
  rfl
theorem s261 (pattern : Twelve) : d157 (change pattern 12 12) = d157 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d1 (change pattern 12 12)) = d157 pattern
  rw [s20, s1]
  rfl
theorem s262 (pattern : Twelve) : d161 (change pattern 12 12) = d161 pattern := by
  change (if pattern.k then d157 (change pattern 12 12) else d1 (change pattern 12 12)) = d161 pattern
  rw [s261, s1]
  rfl
theorem s263 (pattern : Twelve) : d171 (change pattern 12 12) = d171 pattern := by
  change (if pattern.i then d161 (change pattern 12 12) else d0 (change pattern 12 12)) = d171 pattern
  rw [s262, s0]
  rfl
theorem s264 (pattern : Twelve) : d158 (change pattern 12 12) = d158 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d0 (change pattern 12 12)) = d158 pattern
  rw [s20, s0]
  rfl
theorem s265 (pattern : Twelve) : d162 (change pattern 12 12) = d162 pattern := by
  change (if pattern.k then d158 (change pattern 12 12) else d0 (change pattern 12 12)) = d162 pattern
  rw [s264, s0]
  rfl
theorem s266 (pattern : Twelve) : d163 (change pattern 12 12) = d163 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d157 (change pattern 12 12)) = d163 pattern
  rw [s20, s261]
  rfl
theorem s267 (pattern : Twelve) : d172 (change pattern 12 12) = d172 pattern := by
  change (if pattern.i then d163 (change pattern 12 12) else d162 (change pattern 12 12)) = d172 pattern
  rw [s266, s265]
  rfl
theorem s268 (pattern : Twelve) : d185 (change pattern 12 12) = d185 pattern := by
  change (if pattern.h then d172 (change pattern 12 12) else d171 (change pattern 12 12)) = d185 pattern
  rw [s267, s263]
  rfl
theorem s269 (pattern : Twelve) : d164 (change pattern 12 12) = d164 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d158 (change pattern 12 12)) = d164 pattern
  rw [s20, s264]
  rfl
theorem s270 (pattern : Twelve) : d173 (change pattern 12 12) = d173 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d164 (change pattern 12 12)) = d173 pattern
  rw [s20, s269]
  rfl
theorem s271 (pattern : Twelve) : d186 (change pattern 12 12) = d186 pattern := by
  change (if pattern.h then d173 (change pattern 12 12) else d172 (change pattern 12 12)) = d186 pattern
  rw [s270, s267]
  rfl
theorem s272 (pattern : Twelve) : d198 (change pattern 12 12) = d198 pattern := by
  change (if pattern.f then d186 (change pattern 12 12) else d185 (change pattern 12 12)) = d198 pattern
  rw [s271, s268]
  rfl
theorem s273 (pattern : Twelve) : d908 (change pattern 12 12) = d908 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d173 (change pattern 12 12)) = d908 pattern
  rw [s20, s270]
  rfl
theorem s274 (pattern : Twelve) : d909 (change pattern 12 12) = d909 pattern := by
  change (if pattern.f then d908 (change pattern 12 12) else d186 (change pattern 12 12)) = d909 pattern
  rw [s273, s271]
  rfl
theorem s275 (pattern : Twelve) : d912 (change pattern 12 12) = d912 pattern := by
  change (if pattern.e then d909 (change pattern 12 12) else d198 (change pattern 12 12)) = d912 pattern
  rw [s274, s272]
  rfl
theorem s276 (pattern : Twelve) : d160 (change pattern 12 12) = d160 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d2 (change pattern 12 12)) = d160 pattern
  rw [s20, s9]
  rfl
theorem s277 (pattern : Twelve) : d166 (change pattern 12 12) = d166 pattern := by
  change (if pattern.k then d160 (change pattern 12 12) else d2 (change pattern 12 12)) = d166 pattern
  rw [s276, s9]
  rfl
theorem s278 (pattern : Twelve) : d159 (change pattern 12 12) = d159 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d3 (change pattern 12 12)) = d159 pattern
  rw [s20, s11]
  rfl
theorem s279 (pattern : Twelve) : d167 (change pattern 12 12) = d167 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d159 (change pattern 12 12)) = d167 pattern
  rw [s20, s278]
  rfl
theorem s280 (pattern : Twelve) : d175 (change pattern 12 12) = d175 pattern := by
  change (if pattern.i then d167 (change pattern 12 12) else d166 (change pattern 12 12)) = d175 pattern
  rw [s279, s277]
  rfl
theorem s281 (pattern : Twelve) : d168 (change pattern 12 12) = d168 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d160 (change pattern 12 12)) = d168 pattern
  rw [s20, s276]
  rfl
theorem s282 (pattern : Twelve) : d176 (change pattern 12 12) = d176 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d168 (change pattern 12 12)) = d176 pattern
  rw [s20, s281]
  rfl
theorem s283 (pattern : Twelve) : d188 (change pattern 12 12) = d188 pattern := by
  change (if pattern.h then d176 (change pattern 12 12) else d175 (change pattern 12 12)) = d188 pattern
  rw [s282, s280]
  rfl
theorem s284 (pattern : Twelve) : d189 (change pattern 12 12) = d189 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d176 (change pattern 12 12)) = d189 pattern
  rw [s20, s282]
  rfl
theorem s285 (pattern : Twelve) : d200 (change pattern 12 12) = d200 pattern := by
  change (if pattern.f then d189 (change pattern 12 12) else d188 (change pattern 12 12)) = d200 pattern
  rw [s284, s283]
  rfl
theorem s286 (pattern : Twelve) : d910 (change pattern 12 12) = d910 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d189 (change pattern 12 12)) = d910 pattern
  rw [s20, s284]
  rfl
theorem s287 (pattern : Twelve) : d913 (change pattern 12 12) = d913 pattern := by
  change (if pattern.e then d910 (change pattern 12 12) else d200 (change pattern 12 12)) = d913 pattern
  rw [s286, s285]
  rfl
theorem s288 (pattern : Twelve) : d917 (change pattern 12 12) = d917 pattern := by
  change (if pattern.j then d913 (change pattern 12 12) else d912 (change pattern 12 12)) = d917 pattern
  rw [s287, s275]
  rfl
theorem s289 (pattern : Twelve) : d170 (change pattern 12 12) = d170 pattern := by
  change (if pattern.k then d6 (change pattern 12 12) else d13 (change pattern 12 12)) = d170 pattern
  rw [s20, s56]
  rfl
theorem s290 (pattern : Twelve) : d178 (change pattern 12 12) = d178 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d170 (change pattern 12 12)) = d178 pattern
  rw [s20, s289]
  rfl
theorem s291 (pattern : Twelve) : d191 (change pattern 12 12) = d191 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d178 (change pattern 12 12)) = d191 pattern
  rw [s20, s290]
  rfl
theorem s292 (pattern : Twelve) : d202 (change pattern 12 12) = d202 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d191 (change pattern 12 12)) = d202 pattern
  rw [s20, s291]
  rfl
theorem s293 (pattern : Twelve) : d914 (change pattern 12 12) = d914 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d202 (change pattern 12 12)) = d914 pattern
  rw [s20, s292]
  rfl
theorem s294 (pattern : Twelve) : d918 (change pattern 12 12) = d918 pattern := by
  change (if pattern.j then d914 (change pattern 12 12) else d913 (change pattern 12 12)) = d918 pattern
  rw [s293, s287]
  rfl
theorem s295 (pattern : Twelve) : d921 (change pattern 12 12) = d921 pattern := by
  change (if pattern.d then d918 (change pattern 12 12) else d917 (change pattern 12 12)) = d921 pattern
  rw [s294, s288]
  rfl
theorem s296 (pattern : Twelve) : d165 (change pattern 12 12) = d165 pattern := by
  change (if pattern.k then d159 (change pattern 12 12) else d3 (change pattern 12 12)) = d165 pattern
  rw [s278, s11]
  rfl
theorem s297 (pattern : Twelve) : d180 (change pattern 12 12) = d180 pattern := by
  change (if pattern.i then d170 (change pattern 12 12) else d165 (change pattern 12 12)) = d180 pattern
  rw [s289, s296]
  rfl
theorem s298 (pattern : Twelve) : d181 (change pattern 12 12) = d181 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d167 (change pattern 12 12)) = d181 pattern
  rw [s20, s279]
  rfl
theorem s299 (pattern : Twelve) : d193 (change pattern 12 12) = d193 pattern := by
  change (if pattern.h then d181 (change pattern 12 12) else d180 (change pattern 12 12)) = d193 pattern
  rw [s298, s297]
  rfl
end NetHack.Sokoban21.Diagram
