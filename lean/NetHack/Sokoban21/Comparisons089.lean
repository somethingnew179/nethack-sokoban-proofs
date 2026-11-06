/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons088
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12460 (pattern : Twelve) (guard : d1865 pattern = 1) : d1120 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12458 pattern childGuard
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12459 pattern childGuard
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12461 (pattern : Twelve) (guard : d1865 pattern = 1) : d1133 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12455 pattern childGuard
    simpa only [d1133, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12460 pattern childGuard
    simpa only [d1133, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12462 (pattern : Twelve) (guard : d1865 pattern = 1) : d1152 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12453 pattern childGuard
    simpa only [d1152, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12461 pattern childGuard
    simpa only [d1152, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12463 (pattern : Twelve) (guard : d1865 pattern = 1) : d1121 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12261 pattern childGuard
    simpa only [d1121, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12302 pattern childGuard
    simpa only [d1121, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12464 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d1865, d480, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12397 pattern childGuard
    simpa only [d1865, d480, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12465 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d1865, d487, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12420 pattern childGuard
    simpa only [d1865, d487, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12466 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12464 pattern childGuard
    simpa only [d509, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12465 pattern childGuard
    simpa only [d509, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12467 (pattern : Twelve) (guard : d1865 pattern = 1) : d1110 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12450 pattern childGuard
    simpa only [d1110, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1110, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12468 (pattern : Twelve) (guard : d1865 pattern = 1) : d1122 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12466 pattern childGuard
    simpa only [d1122, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12467 pattern childGuard
    simpa only [d1122, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12469 (pattern : Twelve) (guard : d1865 pattern = 1) : d1134 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12463 pattern childGuard
    simpa only [d1134, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12468 pattern childGuard
    simpa only [d1134, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12470 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d515, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d515, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12471 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d544, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12470 pattern childGuard
    simpa only [d544, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12472 (pattern : Twelve) (guard : d1865 pattern = 1) : d1135 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12471 pattern childGuard
    simpa only [d1135, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12460 pattern childGuard
    simpa only [d1135, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12473 (pattern : Twelve) (guard : d1865 pattern = 1) : d1153 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12469 pattern childGuard
    simpa only [d1153, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12472 pattern childGuard
    simpa only [d1153, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12474 (pattern : Twelve) (guard : d1865 pattern = 1) : d1164 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12462 pattern childGuard
    simpa only [d1164, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12473 pattern childGuard
    simpa only [d1164, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12475 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12464 pattern childGuard
    simpa only [d513, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d513, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12476 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12475 pattern childGuard
    simpa only [d1123, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12451 pattern childGuard
    simpa only [d1123, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12477 (pattern : Twelve) (guard : d1865 pattern = 1) : d1136 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12289 pattern childGuard
    simpa only [d1136, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12476 pattern childGuard
    simpa only [d1136, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12478 (pattern : Twelve) (guard : d1865 pattern = 1) : d1137 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d1137, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12460 pattern childGuard
    simpa only [d1137, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12479 (pattern : Twelve) (guard : d1865 pattern = 1) : d1154 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12477 pattern childGuard
    simpa only [d1154, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12478 pattern childGuard
    simpa only [d1154, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12480 (pattern : Twelve) (guard : d1865 pattern = 1) : d1138 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1138, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12468 pattern childGuard
    simpa only [d1138, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12481 (pattern : Twelve) (guard : d1865 pattern = 1) : d1155 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12480 pattern childGuard
    simpa only [d1155, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12472 pattern childGuard
    simpa only [d1155, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12482 (pattern : Twelve) (guard : d1865 pattern = 1) : d1165 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12479 pattern childGuard
    simpa only [d1165, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12481 pattern childGuard
    simpa only [d1165, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12483 (pattern : Twelve) (guard : d1865 pattern = 1) : d1173 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12474 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12482 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12484 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12450 pattern childGuard
    simpa only [d1111, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12421 pattern childGuard
    simpa only [d1111, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12485 (pattern : Twelve) (guard : d1865 pattern = 1) : d1124 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12466 pattern childGuard
    simpa only [d1124, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12484 pattern childGuard
    simpa only [d1124, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12486 (pattern : Twelve) (guard : d1865 pattern = 1) : d1139 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12323 pattern childGuard
    simpa only [d1139, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12485 pattern childGuard
    simpa only [d1139, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12487 (pattern : Twelve) (guard : d1865 pattern = 1) : d1140 pattern ≤ (1 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d1140, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12460 pattern childGuard
    simpa only [d1140, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12488 (pattern : Twelve) (guard : d1865 pattern = 1) : d1156 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12486 pattern childGuard
    simpa only [d1156, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12487 pattern childGuard
    simpa only [d1156, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12489 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12490 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12489 pattern childGuard
    simpa only [d1865, d494, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d494, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12491 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12465 pattern childGuard
    simpa only [d521, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12490 pattern childGuard
    simpa only [d521, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12492 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12069 pattern childGuard
    simpa only [d1865, d1106, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12420 pattern childGuard
    simpa only [d1865, d1106, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12493 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12492 pattern childGuard
    simpa only [d1112, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1112, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12494 (pattern : Twelve) (guard : d1865 pattern = 1) : d1125 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12491 pattern childGuard
    simpa only [d1125, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12493 pattern childGuard
    simpa only [d1125, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12495 (pattern : Twelve) (guard : d1865 pattern = 1) : d1141 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d1141, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12494 pattern childGuard
    simpa only [d1141, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12496 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12272 pattern childGuard
    simpa only [d520, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d520, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12497 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12344 pattern childGuard
    simpa only [d549, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12496 pattern childGuard
    simpa only [d549, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12498 (pattern : Twelve) (guard : d1865 pattern = 1) : d1113 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12457 pattern childGuard
    simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12263 pattern childGuard
    simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12499 (pattern : Twelve) (guard : d1865 pattern = 1) : d178 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12263 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12500 (pattern : Twelve) (guard : d1865 pattern = 1) : d1126 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12498 pattern childGuard
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12499 pattern childGuard
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12501 (pattern : Twelve) (guard : d1865 pattern = 1) : d1142 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12497 pattern childGuard
    simpa only [d1142, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12500 pattern childGuard
    simpa only [d1142, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12502 (pattern : Twelve) (guard : d1865 pattern = 1) : d1157 pattern ≤ (1 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12495 pattern childGuard
    simpa only [d1157, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12501 pattern childGuard
    simpa only [d1157, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12503 (pattern : Twelve) (guard : d1865 pattern = 1) : d1166 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12488 pattern childGuard
    simpa only [d1166, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12502 pattern childGuard
    simpa only [d1166, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12504 (pattern : Twelve) (guard : d1865 pattern = 1) : d1167 pattern ≤ (1 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12481 pattern childGuard
    simpa only [d1167, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1167, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12505 (pattern : Twelve) (guard : d1865 pattern = 1) : d1174 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12503 pattern childGuard
    simpa only [d1174, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12504 pattern childGuard
    simpa only [d1174, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12506 (pattern : Twelve) (guard : d1865 pattern = 1) : d1177 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12483 pattern childGuard
    simpa only [d1177, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12505 pattern childGuard
    simpa only [d1177, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12507 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1143, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12476 pattern childGuard
    simpa only [d1143, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12508 (pattern : Twelve) (guard : d1865 pattern = 1) : d1158 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12507 pattern childGuard
    simpa only [d1158, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12478 pattern childGuard
    simpa only [d1158, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12509 (pattern : Twelve) (guard : d1865 pattern = 1) : d1168 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12508 pattern childGuard
    simpa only [d1168, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12481 pattern childGuard
    simpa only [d1168, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12510 (pattern : Twelve) (guard : d1865 pattern = 1) : d1144 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1144, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12485 pattern childGuard
    simpa only [d1144, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12511 (pattern : Twelve) (guard : d1865 pattern = 1) : d1159 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12510 pattern childGuard
    simpa only [d1159, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12487 pattern childGuard
    simpa only [d1159, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12512 (pattern : Twelve) (guard : d1865 pattern = 1) : d1169 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12511 pattern childGuard
    simpa only [d1169, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12502 pattern childGuard
    simpa only [d1169, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12513 (pattern : Twelve) (guard : d1865 pattern = 1) : d1175 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12512 pattern childGuard
    simpa only [d1175, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12504 pattern childGuard
    simpa only [d1175, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12514 (pattern : Twelve) (guard : d1865 pattern = 1) : d1178 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12509 pattern childGuard
    simpa only [d1178, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12513 pattern childGuard
    simpa only [d1178, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12515 (pattern : Twelve) (guard : d1865 pattern = 1) : d1180 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12506 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12514 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12516 (pattern : Twelve) (guard : d1865 pattern = 1) : d1181 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12515 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12514 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12517 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d16 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12518 (pattern : Twelve) (guard : d1865 pattern = 1) : d479 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11332 pattern childGuard
    simpa only [d1865, d479, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12517 pattern childGuard
    simpa only [d1865, d479, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12519 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12464 pattern childGuard
    simpa only [d513, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d513, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12520 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12450 pattern childGuard
    simpa only [d1108, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1108, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12521 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12519 pattern childGuard
    simpa only [d1123, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12520 pattern childGuard
    simpa only [d1123, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12522 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (1 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1143, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12521 pattern childGuard
    simpa only [d1143, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12523 (pattern : Twelve) (guard : d1865 pattern = 1) : d1114 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12456 pattern childGuard
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12263 pattern childGuard
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12524 (pattern : Twelve) (guard : d1865 pattern = 1) : d1127 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12523 pattern childGuard
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12459 pattern childGuard
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12525 (pattern : Twelve) (guard : d1865 pattern = 1) : d1145 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d1145, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12524 pattern childGuard
    simpa only [d1145, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12526 (pattern : Twelve) (guard : d1865 pattern = 1) : d1160 pattern ≤ (1 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12522 pattern childGuard
    simpa only [d1160, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12525 pattern childGuard
    simpa only [d1160, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12527 (pattern : Twelve) (guard : d1865 pattern = 1) : d1115 pattern ≤ (1 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12464 pattern childGuard
    simpa only [d1115, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12492 pattern childGuard
    simpa only [d1115, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12528 (pattern : Twelve) (guard : d1865 pattern = 1) : d1128 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12527 pattern childGuard
    simpa only [d1128, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12467 pattern childGuard
    simpa only [d1128, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12529 (pattern : Twelve) (guard : d1865 pattern = 1) : d1146 pattern ≤ (1 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1146, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12528 pattern childGuard
    simpa only [d1146, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12530 (pattern : Twelve) (guard : d1865 pattern = 1) : d1147 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12471 pattern childGuard
    simpa only [d1147, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12524 pattern childGuard
    simpa only [d1147, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12531 (pattern : Twelve) (guard : d1865 pattern = 1) : d1161 pattern ≤ (1 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12529 pattern childGuard
    simpa only [d1161, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12530 pattern childGuard
    simpa only [d1161, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12532 (pattern : Twelve) (guard : d1865 pattern = 1) : d1170 pattern ≤ (1 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12526 pattern childGuard
    simpa only [d1170, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12531 pattern childGuard
    simpa only [d1170, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12533 (pattern : Twelve) (guard : d1865 pattern = 1) : d1116 pattern ≤ (1 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12450 pattern childGuard
    simpa only [d1116, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12490 pattern childGuard
    simpa only [d1116, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12534 (pattern : Twelve) (guard : d1865 pattern = 1) : d1129 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12527 pattern childGuard
    simpa only [d1129, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12533 pattern childGuard
    simpa only [d1129, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12535 (pattern : Twelve) (guard : d1865 pattern = 1) : d1148 pattern ≤ (1 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1148, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12534 pattern childGuard
    simpa only [d1148, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12536 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12537 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11363 pattern childGuard
    simpa only [d1865, d492, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12536 pattern childGuard
    simpa only [d1865, d492, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12538 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (1 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d518, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12537 pattern childGuard
    simpa only [d518, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12539 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d556, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12538 pattern childGuard
    simpa only [d556, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12540 (pattern : Twelve) (guard : d1865 pattern = 1) : d1149 pattern ≤ (1 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12539 pattern childGuard
    simpa only [d1149, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12524 pattern childGuard
    simpa only [d1149, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12541 (pattern : Twelve) (guard : d1865 pattern = 1) : d1162 pattern ≤ (1 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12535 pattern childGuard
    simpa only [d1162, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12540 pattern childGuard
    simpa only [d1162, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12542 (pattern : Twelve) (guard : d1865 pattern = 1) : d530 pattern ≤ (1 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12465 pattern childGuard
    simpa only [d530, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d530, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12543 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12544 (pattern : Twelve) (guard : d1865 pattern = 1) : d1107 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1107, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12543 pattern childGuard
    simpa only [d1865, d1107, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1107, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d1107, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12545 (pattern : Twelve) (guard : d1865 pattern = 1) : d1117 pattern ≤ (1 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12544 pattern childGuard
    simpa only [d1117, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1117, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12546 (pattern : Twelve) (guard : d1865 pattern = 1) : d1130 pattern ≤ (1 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12542 pattern childGuard
    simpa only [d1130, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12545 pattern childGuard
    simpa only [d1130, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12547 (pattern : Twelve) (guard : d1865 pattern = 1) : d1150 pattern ≤ (1 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d1150, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12546 pattern childGuard
    simpa only [d1150, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12548 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (1 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12272 pattern childGuard
    simpa only [d528, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12427 pattern childGuard
    simpa only [d528, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12549 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12537 pattern childGuard
    simpa only [d529, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d529, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12550 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12548 pattern childGuard
    simpa only [d559, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12549 pattern childGuard
    simpa only [d559, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12551 (pattern : Twelve) (guard : d1865 pattern = 1) : d1131 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12459 pattern childGuard
    simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12552 (pattern : Twelve) (guard : d1865 pattern = 1) : d1151 pattern ≤ (1 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12550 pattern childGuard
    simpa only [d1151, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12551 pattern childGuard
    simpa only [d1151, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12553 (pattern : Twelve) (guard : d1865 pattern = 1) : d1163 pattern ≤ (1 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12547 pattern childGuard
    simpa only [d1163, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12552 pattern childGuard
    simpa only [d1163, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12554 (pattern : Twelve) (guard : d1865 pattern = 1) : d1171 pattern ≤ (1 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12541 pattern childGuard
    simpa only [d1171, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12553 pattern childGuard
    simpa only [d1171, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12555 (pattern : Twelve) (guard : d1865 pattern = 1) : d1172 pattern ≤ (1 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12531 pattern childGuard
    simpa only [d1172, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1172, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12556 (pattern : Twelve) (guard : d1865 pattern = 1) : d1176 pattern ≤ (1 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12554 pattern childGuard
    simpa only [d1176, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12555 pattern childGuard
    simpa only [d1176, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12557 (pattern : Twelve) (guard : d1865 pattern = 1) : d1179 pattern ≤ (1 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12532 pattern childGuard
    simpa only [d1179, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12556 pattern childGuard
    simpa only [d1179, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12558 (pattern : Twelve) (guard : d1865 pattern = 1) : d1182 pattern ≤ (1 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12516 pattern childGuard
    simpa only [d1182, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12557 pattern childGuard
    simpa only [d1182, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12559 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11224 pattern childGuard
    simpa only [d1865, d1105, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12517 pattern childGuard
    simpa only [d1865, d1105, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12560 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12559 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12561 (pattern : Twelve) (guard : d1865 pattern = 1) : d1505 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12560 pattern childGuard
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12562 (pattern : Twelve) (guard : d1865 pattern = 1) : d1517 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12455 pattern childGuard
    simpa only [d1517, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12561 pattern childGuard
    simpa only [d1517, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12563 (pattern : Twelve) (guard : d1865 pattern = 1) : d1518 pattern ≤ (1 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12241 pattern childGuard
    simpa only [d1518, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1518, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12564 (pattern : Twelve) (guard : d1865 pattern = 1) : d1532 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12562 pattern childGuard
    simpa only [d1532, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12563 pattern childGuard
    simpa only [d1532, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12565 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11277 pattern childGuard
    simpa only [d1865, d1106, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12536 pattern childGuard
    simpa only [d1865, d1106, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12566 (pattern : Twelve) (guard : d1865 pattern = 1) : d1495 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12559 pattern childGuard
    simpa only [d1495, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12565 pattern childGuard
    simpa only [d1495, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12567 (pattern : Twelve) (guard : d1865 pattern = 1) : d1496 pattern ≤ (1 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1496, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1496, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12568 (pattern : Twelve) (guard : d1865 pattern = 1) : d1506 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12566 pattern childGuard
    simpa only [d1506, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12567 pattern childGuard
    simpa only [d1506, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12569 (pattern : Twelve) (guard : d1865 pattern = 1) : d1519 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12471 pattern childGuard
    simpa only [d1519, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12568 pattern childGuard
    simpa only [d1519, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12570 (pattern : Twelve) (guard : d1865 pattern = 1) : d1109 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12241 pattern childGuard
    simpa only [d1109, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12345 pattern childGuard
    simpa only [d1109, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12571 (pattern : Twelve) (guard : d1865 pattern = 1) : d1507 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12570 pattern childGuard
    simpa only [d1507, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12243 pattern childGuard
    simpa only [d1507, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12572 (pattern : Twelve) (guard : d1865 pattern = 1) : d1520 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12571 pattern childGuard
    simpa only [d1520, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1520, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12573 (pattern : Twelve) (guard : d1865 pattern = 1) : d1533 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12569 pattern childGuard
    simpa only [d1533, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12572 pattern childGuard
    simpa only [d1533, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12574 (pattern : Twelve) (guard : d1865 pattern = 1) : d1541 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12564 pattern childGuard
    simpa only [d1541, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12573 pattern childGuard
    simpa only [d1541, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12575 (pattern : Twelve) (guard : d1865 pattern = 1) : d1521 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d1521, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12561 pattern childGuard
    simpa only [d1521, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12576 (pattern : Twelve) (guard : d1865 pattern = 1) : d1534 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12575 pattern childGuard
    simpa only [d1534, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12563 pattern childGuard
    simpa only [d1534, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12577 (pattern : Twelve) (guard : d1865 pattern = 1) : d1542 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12576 pattern childGuard
    simpa only [d1542, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12573 pattern childGuard
    simpa only [d1542, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12578 (pattern : Twelve) (guard : d1865 pattern = 1) : d1548 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12574 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12577 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12579 (pattern : Twelve) (guard : d1865 pattern = 1) : d1497 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1497, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12537 pattern childGuard
    simpa only [d1497, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12580 (pattern : Twelve) (guard : d1865 pattern = 1) : d1508 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12566 pattern childGuard
    simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12579 pattern childGuard
    simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12581 (pattern : Twelve) (guard : d1865 pattern = 1) : d1522 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d1522, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12580 pattern childGuard
    simpa only [d1522, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12582 (pattern : Twelve) (guard : d1865 pattern = 1) : d1523 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12570 pattern childGuard
    simpa only [d1523, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1523, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12583 (pattern : Twelve) (guard : d1865 pattern = 1) : d1535 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12581 pattern childGuard
    simpa only [d1535, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12582 pattern childGuard
    simpa only [d1535, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12584 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12585 (pattern : Twelve) (guard : d1865 pattern = 1) : d1493 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1493, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d1865, d1493, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1493, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d1493, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12586 (pattern : Twelve) (guard : d1865 pattern = 1) : d1498 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12565 pattern childGuard
    simpa only [d1498, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12585 pattern childGuard
    simpa only [d1498, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12587 (pattern : Twelve) (guard : d1865 pattern = 1) : d1509 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12586 pattern childGuard
    simpa only [d1509, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12549 pattern childGuard
    simpa only [d1509, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12588 (pattern : Twelve) (guard : d1865 pattern = 1) : d1524 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12497 pattern childGuard
    simpa only [d1524, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12587 pattern childGuard
    simpa only [d1524, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12589 (pattern : Twelve) (guard : d1865 pattern = 1) : d1113 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12345 pattern childGuard
    simpa only [d1113, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12263 pattern childGuard
    simpa only [d1113, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12590 (pattern : Twelve) (guard : d1865 pattern = 1) : d1510 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12589 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12346 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12591 (pattern : Twelve) (guard : d1865 pattern = 1) : d1525 pattern ≤ (1 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12590 pattern childGuard
    simpa only [d1525, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1525, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12592 (pattern : Twelve) (guard : d1865 pattern = 1) : d1536 pattern ≤ (1 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12588 pattern childGuard
    simpa only [d1536, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12591 pattern childGuard
    simpa only [d1536, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12593 (pattern : Twelve) (guard : d1865 pattern = 1) : d1543 pattern ≤ (1 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12583 pattern childGuard
    simpa only [d1543, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12592 pattern childGuard
    simpa only [d1543, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12594 (pattern : Twelve) (guard : d1865 pattern = 1) : d1544 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12573 pattern childGuard
    simpa only [d1544, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1544, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12595 (pattern : Twelve) (guard : d1865 pattern = 1) : d1549 pattern ≤ (1 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12593 pattern childGuard
    simpa only [d1549, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12594 pattern childGuard
    simpa only [d1549, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12596 (pattern : Twelve) (guard : d1865 pattern = 1) : d1551 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12578 pattern childGuard
    simpa only [d1551, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12595 pattern childGuard
    simpa only [d1551, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12597 (pattern : Twelve) (guard : d1865 pattern = 1) : d1552 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12577 pattern childGuard
    simpa only [d1552, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12595 pattern childGuard
    simpa only [d1552, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12598 (pattern : Twelve) (guard : d1865 pattern = 1) : d1554 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12596 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12597 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12599 (pattern : Twelve) (guard : d1865 pattern = 1) : d1555 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12598 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12597 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
