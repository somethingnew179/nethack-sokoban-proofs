/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons150
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21140 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (2 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21139 pattern childGuard
    simpa only [d852, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13376 pattern childGuard
    simpa only [d852, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21141 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (2 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21138 pattern childGuard
    simpa only [d1259, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21140 pattern childGuard
    simpa only [d1259, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21142 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (2 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21073 pattern childGuard
    simpa only [d1251, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21067 pattern childGuard
    simpa only [d1251, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21143 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (2 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21066 pattern childGuard
    simpa only [d1256, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21142 pattern childGuard
    simpa only [d1256, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21144 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21073 pattern childGuard
    simpa only [d787, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21070 pattern childGuard
    simpa only [d787, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21145 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (2 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13470 pattern childGuard
    simpa only [d1252, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21122 pattern childGuard
    simpa only [d1252, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21146 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21144 pattern childGuard
    simpa only [d1257, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21145 pattern childGuard
    simpa only [d1257, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21147 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (2 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21143 pattern childGuard
    simpa only [d1260, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21146 pattern childGuard
    simpa only [d1260, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21148 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (2 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21141 pattern childGuard
    simpa only [d1262, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21147 pattern childGuard
    simpa only [d1262, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21149 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (2 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13402 pattern childGuard
    simpa only [d1263, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1263, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21150 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (2 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21148 pattern childGuard
    simpa only [d1264, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21149 pattern childGuard
    simpa only [d1264, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21151 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (2 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21136 pattern childGuard
    simpa only [d1265, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21150 pattern childGuard
    simpa only [d1265, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21152 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (2 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21129 pattern childGuard
    simpa only [d1266, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21151 pattern childGuard
    simpa only [d1266, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21153 (pattern : Twelve) (guard : d1879 pattern = 1) : d1267 pattern ≤ (2 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1879, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21084 pattern childGuard
    simpa only [d1879, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1879, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21152 pattern childGuard
    simpa only [d1879, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21154 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (2 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21155 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (2 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13409 pattern childGuard
    simpa only [d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14415 pattern childGuard
    simpa only [d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21156 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14415 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21157 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (2 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21155 pattern childGuard
    simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21156 pattern childGuard
    simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21158 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (2 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21157 pattern childGuard
    simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21159 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (2 : Int) + d1294 pattern := by
  omega
theorem c21160 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (2 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21158 pattern childGuard
    simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21159 pattern childGuard
    simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21161 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d117 pattern := by
  omega
theorem c21162 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21095 pattern childGuard
    simpa only [d119, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21161 pattern childGuard
    simpa only [d119, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21163 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (2 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13409 pattern childGuard
    simpa only [d1327, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21162 pattern childGuard
    simpa only [d1327, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21164 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (2 : Int) + d1280 pattern := by
  omega
theorem c21165 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (2 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21163 pattern childGuard
    simpa only [d1334, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21164 pattern childGuard
    simpa only [d1334, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21166 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (2 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21101 pattern childGuard
    simpa only [d1340, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21165 pattern childGuard
    simpa only [d1340, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21167 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (2 : Int) + d1296 pattern := by
  omega
theorem c21168 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (2 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21166 pattern childGuard
    simpa only [d1346, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21167 pattern childGuard
    simpa only [d1346, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21169 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (2 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21160 pattern childGuard
    simpa only [d1349, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21168 pattern childGuard
    simpa only [d1349, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21170 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (2 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1328, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14401 pattern childGuard
    simpa only [d1328, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21171 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (2 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21163 pattern childGuard
    simpa only [d1335, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21170 pattern childGuard
    simpa only [d1335, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21172 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (2 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d1341, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21171 pattern childGuard
    simpa only [d1341, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21173 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (2 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21032 pattern childGuard
    simpa only [d1329, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21174 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (2 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21173 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21175 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (2 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21174 pattern childGuard
    simpa only [d1342, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1342, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21176 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (2 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21172 pattern childGuard
    simpa only [d1347, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21175 pattern childGuard
    simpa only [d1347, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21177 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (2 : Int) + d830 pattern := by
  omega
theorem c21178 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (2 : Int) + d1276 pattern := by
  omega
theorem c21179 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (2 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21178 pattern childGuard
    simpa only [d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14434 pattern childGuard
    simpa only [d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21180 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (2 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14401 pattern childGuard
    simpa only [d1331, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1331, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21181 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (2 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21179 pattern childGuard
    simpa only [d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21180 pattern childGuard
    simpa only [d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21182 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (2 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21177 pattern childGuard
    simpa only [d1343, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21181 pattern childGuard
    simpa only [d1343, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21183 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21016 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21184 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21183 pattern childGuard
    simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13468 pattern childGuard
    simpa only [d22, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21185 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21184 pattern childGuard
    simpa only [d1332, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21186 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (2 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21185 pattern childGuard
    simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21033 pattern childGuard
    simpa only [d1338, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21187 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (2 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21186 pattern childGuard
    simpa only [d1344, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1344, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21188 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (2 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21182 pattern childGuard
    simpa only [d1348, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21187 pattern childGuard
    simpa only [d1348, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21189 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (2 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21176 pattern childGuard
    simpa only [d1350, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21188 pattern childGuard
    simpa only [d1350, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21190 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (2 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21168 pattern childGuard
    simpa only [d1351, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1351, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21191 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (2 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21189 pattern childGuard
    simpa only [d1352, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21190 pattern childGuard
    simpa only [d1352, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21192 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (2 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21169 pattern childGuard
    simpa only [d1353, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21191 pattern childGuard
    simpa only [d1353, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21193 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (2 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13422 pattern childGuard
    simpa only [d1616, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d1616, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21194 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (2 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21193 pattern childGuard
    simpa only [d1619, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d1619, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21195 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (2 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d1622, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21194 pattern childGuard
    simpa only [d1622, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21196 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (2 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d1617, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13305 pattern childGuard
    simpa only [d1617, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21197 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (2 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21196 pattern childGuard
    simpa only [d1623, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1623, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21198 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (2 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21195 pattern childGuard
    simpa only [d1627, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21197 pattern childGuard
    simpa only [d1627, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21199 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (2 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21198 pattern childGuard
    simpa only [d1630, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13447 pattern childGuard
    simpa only [d1630, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21200 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (2 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13414 pattern childGuard
    simpa only [d1618, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14264 pattern childGuard
    simpa only [d1618, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21201 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (2 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13425 pattern childGuard
    simpa only [d1620, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21200 pattern childGuard
    simpa only [d1620, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21202 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (2 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13306 pattern childGuard
    simpa only [d1624, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21201 pattern childGuard
    simpa only [d1624, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21203 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (2 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13374 pattern childGuard
    simpa only [d1292, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21073 pattern childGuard
    simpa only [d1292, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21204 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (2 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21203 pattern childGuard
    simpa only [d1304, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1304, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21205 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (2 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21202 pattern childGuard
    simpa only [d1628, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21204 pattern childGuard
    simpa only [d1628, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21206 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (2 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21073 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13343 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21207 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (2 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13424 pattern childGuard
    simpa only [d1331, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14434 pattern childGuard
    simpa only [d1331, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21208 (pattern : Twelve) (guard : d1 pattern = 1) : d182 pattern ≤ (2 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14264 pattern childGuard
    simpa only [d182, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d182, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21209 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (2 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21207 pattern childGuard
    simpa only [d1621, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21208 pattern childGuard
    simpa only [d1621, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21210 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (2 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21206 pattern childGuard
    simpa only [d1625, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21209 pattern childGuard
    simpa only [d1625, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21211 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13470 pattern childGuard
    simpa only [d1252, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21074 pattern childGuard
    simpa only [d1252, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21212 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21211 pattern childGuard
    simpa only [d1626, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1626, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21213 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (2 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21210 pattern childGuard
    simpa only [d1629, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21212 pattern childGuard
    simpa only [d1629, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21214 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (2 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21205 pattern childGuard
    simpa only [d1631, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21213 pattern childGuard
    simpa only [d1631, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21215 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (2 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13447 pattern childGuard
    simpa only [d1632, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1632, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21216 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (2 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21214 pattern childGuard
    simpa only [d1633, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21215 pattern childGuard
    simpa only [d1633, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21217 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (2 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21199 pattern childGuard
    simpa only [d1634, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21216 pattern childGuard
    simpa only [d1634, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21218 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (2 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21192 pattern childGuard
    simpa only [d1635, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21217 pattern childGuard
    simpa only [d1635, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21219 (pattern : Twelve) (guard : d1879 pattern = 1) : d1636 pattern ≤ (2 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1879, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21154 pattern childGuard
    simpa only [d1879, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1879, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21218 pattern childGuard
    simpa only [d1879, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21220 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c21221 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13456 pattern childGuard
    simpa only [d1668, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21222 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (2 : Int) + d1650 pattern := by
  omega
theorem c21223 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21221 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21222 pattern childGuard
    simpa only [d1671, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21224 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (2 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21223 pattern childGuard
    simpa only [d1674, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13621 pattern childGuard
    simpa only [d1674, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21225 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (2 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1665, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d1665, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21226 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (2 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13606 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21225 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21227 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (2 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1669, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21226 pattern childGuard
    simpa only [d1669, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21228 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13612 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21121 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21229 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21228 pattern childGuard
    simpa only [d1300, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1300, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21230 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (2 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21227 pattern childGuard
    simpa only [d1672, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21229 pattern childGuard
    simpa only [d1672, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21231 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d1289 pattern := by
  omega
theorem c21232 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (2 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20591 pattern childGuard
    simpa only [d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14487 pattern childGuard
    simpa only [d128, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21233 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (2 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d183, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d183, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21234 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (2 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21232 pattern childGuard
    simpa only [d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21233 pattern childGuard
    simpa only [d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21235 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (2 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21231 pattern childGuard
    simpa only [d1670, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21234 pattern childGuard
    simpa only [d1670, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21236 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (2 : Int) + d822 pattern := by
  omega
theorem c21237 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21236 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21122 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21238 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (2 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21237 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21239 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (2 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21235 pattern childGuard
    simpa only [d1673, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21238 pattern childGuard
    simpa only [d1673, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21240 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (2 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21230 pattern childGuard
    simpa only [d1675, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21239 pattern childGuard
    simpa only [d1675, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21241 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (2 : Int) + d1662 pattern := by
  omega
theorem c21242 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (2 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21240 pattern childGuard
    simpa only [d1676, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21241 pattern childGuard
    simpa only [d1676, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21243 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (2 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21224 pattern childGuard
    simpa only [d1677, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21242 pattern childGuard
    simpa only [d1677, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21244 (pattern : Twelve) (guard : d1 pattern = 1) : d1814 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d1814, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13455 pattern childGuard
    simpa only [d1814, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21245 (pattern : Twelve) (guard : d1 pattern = 1) : d1815 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13373 pattern childGuard
    simpa only [d1815, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1815, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21246 (pattern : Twelve) (guard : d1 pattern = 1) : d1818 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21244 pattern childGuard
    simpa only [d1818, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21245 pattern childGuard
    simpa only [d1818, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21247 (pattern : Twelve) (guard : d1 pattern = 1) : d1821 pattern ≤ (2 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21246 pattern childGuard
    simpa only [d1821, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13473 pattern childGuard
    simpa only [d1821, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21248 (pattern : Twelve) (guard : d1 pattern = 1) : d1816 pattern ≤ (2 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13374 pattern childGuard
    simpa only [d1816, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13464 pattern childGuard
    simpa only [d1816, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21249 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (2 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13470 pattern childGuard
    simpa only [d1655, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1655, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21250 (pattern : Twelve) (guard : d1 pattern = 1) : d1819 pattern ≤ (2 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21248 pattern childGuard
    simpa only [d1819, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21249 pattern childGuard
    simpa only [d1819, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21251 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (2 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d183, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14487 pattern childGuard
    simpa only [d183, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21252 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (2 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21251 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21233 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21253 (pattern : Twelve) (guard : d1 pattern = 1) : d1817 pattern ≤ (2 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13471 pattern childGuard
    simpa only [d1817, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21252 pattern childGuard
    simpa only [d1817, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21254 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21122 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21255 (pattern : Twelve) (guard : d1 pattern = 1) : d1820 pattern ≤ (2 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21253 pattern childGuard
    simpa only [d1820, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21254 pattern childGuard
    simpa only [d1820, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21256 (pattern : Twelve) (guard : d1 pattern = 1) : d1822 pattern ≤ (2 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21250 pattern childGuard
    simpa only [d1822, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21255 pattern childGuard
    simpa only [d1822, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21257 (pattern : Twelve) (guard : d1 pattern = 1) : d1823 pattern ≤ (2 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13473 pattern childGuard
    simpa only [d1823, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1823, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21258 (pattern : Twelve) (guard : d1 pattern = 1) : d1824 pattern ≤ (2 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21256 pattern childGuard
    simpa only [d1824, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21257 pattern childGuard
    simpa only [d1824, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21259 (pattern : Twelve) (guard : d1 pattern = 1) : d1825 pattern ≤ (2 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21247 pattern childGuard
    simpa only [d1825, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21258 pattern childGuard
    simpa only [d1825, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21260 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (2 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21243 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21259 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21261 (pattern : Twelve) (guard : d1879 pattern = 1) : d1827 pattern ≤ (2 : Int) + d1664 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1879, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21220 pattern childGuard
    simpa only [d1879, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1879, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21260 pattern childGuard
    simpa only [d1879, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21262 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21263 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21264 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21262 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21263 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21265 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (2 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21264 pattern childGuard
    simpa only [d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21266 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (2 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21265 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20291 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21267 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (2 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21266 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21268 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (2 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20285 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21267 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21269 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21270 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21269 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21271 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21270 pattern childGuard
    simpa only [d30, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21272 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (2 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13614 pattern childGuard
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21273 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (2 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21271 pattern childGuard
    simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21272 pattern childGuard
    simpa only [d53, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21274 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (2 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20295 pattern childGuard
    simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21273 pattern childGuard
    simpa only [d74, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21275 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (2 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21276 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21275 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21277 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14593 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21263 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21278 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21277 pattern childGuard
    simpa only [d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21279 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (2 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21278 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20291 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
