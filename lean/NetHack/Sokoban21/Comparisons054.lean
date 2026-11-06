/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons053
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7560 (pattern : Twelve) (guard : d1867 pattern = 1) : d1110 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1110, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1110, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1110, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1110, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7561 (pattern : Twelve) (guard : d1867 pattern = 1) : d1122 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1122, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1122, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1122, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7560 pattern childGuard
    simpa only [d1122, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7562 (pattern : Twelve) (guard : d1867 pattern = 1) : d1134 pattern ≤ (0 : Int) + d1201 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1134, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7559 pattern childGuard
    simpa only [d1134, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1134, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7561 pattern childGuard
    simpa only [d1134, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7563 (pattern : Twelve) (guard : d1867 pattern = 1) : d1135 pattern ≤ (0 : Int) + d1202 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1135, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1135, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1135, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7556 pattern childGuard
    simpa only [d1135, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7564 (pattern : Twelve) (guard : d1867 pattern = 1) : d1153 pattern ≤ (0 : Int) + d1217 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1153, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7562 pattern childGuard
    simpa only [d1153, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1153, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7563 pattern childGuard
    simpa only [d1153, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7565 (pattern : Twelve) (guard : d1867 pattern = 1) : d1164 pattern ≤ (0 : Int) + d1228 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1164, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7558 pattern childGuard
    simpa only [d1164, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1164, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7564 pattern childGuard
    simpa only [d1164, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7566 (pattern : Twelve) (guard : d1867 pattern = 1) : d1123 pattern ≤ (0 : Int) + d1193 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1123, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7434 pattern childGuard
    simpa only [d1123, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1123, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7551 pattern childGuard
    simpa only [d1123, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7567 (pattern : Twelve) (guard : d1867 pattern = 1) : d1136 pattern ≤ (0 : Int) + d1203 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1136, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7437 pattern childGuard
    simpa only [d1136, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1136, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7566 pattern childGuard
    simpa only [d1136, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7568 (pattern : Twelve) (guard : d1867 pattern = 1) : d1137 pattern ≤ (0 : Int) + d1204 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1137, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1137, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1137, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7556 pattern childGuard
    simpa only [d1137, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7569 (pattern : Twelve) (guard : d1867 pattern = 1) : d1154 pattern ≤ (0 : Int) + d1218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1154, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7567 pattern childGuard
    simpa only [d1154, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1154, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7568 pattern childGuard
    simpa only [d1154, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7570 (pattern : Twelve) (guard : d1867 pattern = 1) : d1138 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1138, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1138, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1138, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7561 pattern childGuard
    simpa only [d1138, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7571 (pattern : Twelve) (guard : d1867 pattern = 1) : d1155 pattern ≤ (0 : Int) + d1219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1155, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7570 pattern childGuard
    simpa only [d1155, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1155, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7563 pattern childGuard
    simpa only [d1155, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7572 (pattern : Twelve) (guard : d1867 pattern = 1) : d1165 pattern ≤ (0 : Int) + d1229 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1165, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7569 pattern childGuard
    simpa only [d1165, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1165, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7571 pattern childGuard
    simpa only [d1165, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7573 (pattern : Twelve) (guard : d1867 pattern = 1) : d1173 pattern ≤ (0 : Int) + d1237 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1173, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7565 pattern childGuard
    simpa only [d1173, d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1173, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7572 pattern childGuard
    simpa only [d1173, d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7574 (pattern : Twelve) (guard : d1867 pattern = 1) : d1111 pattern ≤ (0 : Int) + d1185 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1111, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1111, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1111, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7459 pattern childGuard
    simpa only [d1111, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7575 (pattern : Twelve) (guard : d1867 pattern = 1) : d1124 pattern ≤ (0 : Int) + d1194 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1124, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1124, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1124, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7574 pattern childGuard
    simpa only [d1124, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7576 (pattern : Twelve) (guard : d1867 pattern = 1) : d1139 pattern ≤ (0 : Int) + d1205 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1139, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7463 pattern childGuard
    simpa only [d1139, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1139, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7575 pattern childGuard
    simpa only [d1139, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7577 (pattern : Twelve) (guard : d1867 pattern = 1) : d1140 pattern ≤ (0 : Int) + d1206 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1140, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1140, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1140, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7556 pattern childGuard
    simpa only [d1140, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7578 (pattern : Twelve) (guard : d1867 pattern = 1) : d1156 pattern ≤ (0 : Int) + d1220 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1156, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7576 pattern childGuard
    simpa only [d1156, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1156, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7577 pattern childGuard
    simpa only [d1156, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7579 (pattern : Twelve) (guard : d1867 pattern = 1) : d1106 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1106, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d1867, d1106, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1106, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7458 pattern childGuard
    simpa only [d1867, d1106, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7580 (pattern : Twelve) (guard : d1867 pattern = 1) : d1112 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1112, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7579 pattern childGuard
    simpa only [d1112, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1112, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1112, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7581 (pattern : Twelve) (guard : d1867 pattern = 1) : d1125 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1125, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7472 pattern childGuard
    simpa only [d1125, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1125, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7580 pattern childGuard
    simpa only [d1125, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7582 (pattern : Twelve) (guard : d1867 pattern = 1) : d1141 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1141, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d1141, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1141, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7581 pattern childGuard
    simpa only [d1141, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7583 (pattern : Twelve) (guard : d1867 pattern = 1) : d1113 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1113, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d1113, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1113, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7417 pattern childGuard
    simpa only [d1113, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7584 (pattern : Twelve) (guard : d1867 pattern = 1) : d178 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7417 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7585 (pattern : Twelve) (guard : d1867 pattern = 1) : d1126 pattern ≤ (0 : Int) + d1195 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1126, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7583 pattern childGuard
    simpa only [d1126, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1126, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7584 pattern childGuard
    simpa only [d1126, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7586 (pattern : Twelve) (guard : d1867 pattern = 1) : d1142 pattern ≤ (0 : Int) + d1207 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1142, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d1142, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1142, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7585 pattern childGuard
    simpa only [d1142, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7587 (pattern : Twelve) (guard : d1867 pattern = 1) : d1157 pattern ≤ (0 : Int) + d1221 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1157, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7582 pattern childGuard
    simpa only [d1157, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1157, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7586 pattern childGuard
    simpa only [d1157, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7588 (pattern : Twelve) (guard : d1867 pattern = 1) : d1166 pattern ≤ (0 : Int) + d1230 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1166, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7578 pattern childGuard
    simpa only [d1166, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1166, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7587 pattern childGuard
    simpa only [d1166, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7589 (pattern : Twelve) (guard : d1867 pattern = 1) : d1167 pattern ≤ (0 : Int) + d1231 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1167, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7571 pattern childGuard
    simpa only [d1167, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1167, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1167, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7590 (pattern : Twelve) (guard : d1867 pattern = 1) : d1174 pattern ≤ (0 : Int) + d1238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1174, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7588 pattern childGuard
    simpa only [d1174, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1174, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7589 pattern childGuard
    simpa only [d1174, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7591 (pattern : Twelve) (guard : d1867 pattern = 1) : d1177 pattern ≤ (0 : Int) + d1241 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1177, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7573 pattern childGuard
    simpa only [d1177, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1177, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7590 pattern childGuard
    simpa only [d1177, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7592 (pattern : Twelve) (guard : d1867 pattern = 1) : d1143 pattern ≤ (0 : Int) + d1208 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1143, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1143, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1143, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7566 pattern childGuard
    simpa only [d1143, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7593 (pattern : Twelve) (guard : d1867 pattern = 1) : d1158 pattern ≤ (0 : Int) + d1222 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1158, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7592 pattern childGuard
    simpa only [d1158, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1158, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7568 pattern childGuard
    simpa only [d1158, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7594 (pattern : Twelve) (guard : d1867 pattern = 1) : d1168 pattern ≤ (0 : Int) + d1232 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1168, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7593 pattern childGuard
    simpa only [d1168, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1168, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7571 pattern childGuard
    simpa only [d1168, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7595 (pattern : Twelve) (guard : d1867 pattern = 1) : d1144 pattern ≤ (0 : Int) + d1209 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1144, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1144, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1144, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7575 pattern childGuard
    simpa only [d1144, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7596 (pattern : Twelve) (guard : d1867 pattern = 1) : d1159 pattern ≤ (0 : Int) + d1223 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1159, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7595 pattern childGuard
    simpa only [d1159, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1159, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7577 pattern childGuard
    simpa only [d1159, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7597 (pattern : Twelve) (guard : d1867 pattern = 1) : d1169 pattern ≤ (0 : Int) + d1233 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1169, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7596 pattern childGuard
    simpa only [d1169, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1169, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7587 pattern childGuard
    simpa only [d1169, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7598 (pattern : Twelve) (guard : d1867 pattern = 1) : d1175 pattern ≤ (0 : Int) + d1239 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1175, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7597 pattern childGuard
    simpa only [d1175, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1175, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7589 pattern childGuard
    simpa only [d1175, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7599 (pattern : Twelve) (guard : d1867 pattern = 1) : d1178 pattern ≤ (0 : Int) + d1242 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1178, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7594 pattern childGuard
    simpa only [d1178, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1178, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7598 pattern childGuard
    simpa only [d1178, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7600 (pattern : Twelve) (guard : d1867 pattern = 1) : d1180 pattern ≤ (0 : Int) + d1244 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1180, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7591 pattern childGuard
    simpa only [d1180, d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1180, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7599 pattern childGuard
    simpa only [d1180, d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7601 (pattern : Twelve) (guard : d1867 pattern = 1) : d1181 pattern ≤ (0 : Int) + d1245 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1181, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7600 pattern childGuard
    simpa only [d1181, d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1181, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7599 pattern childGuard
    simpa only [d1181, d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7602 (pattern : Twelve) (guard : d1867 pattern = 1) : d1114 pattern ≤ (0 : Int) + d1187 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1114, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1114, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1114, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7417 pattern childGuard
    simpa only [d1114, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7603 (pattern : Twelve) (guard : d1867 pattern = 1) : d1127 pattern ≤ (0 : Int) + d1196 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1127, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7602 pattern childGuard
    simpa only [d1127, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1127, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7476 pattern childGuard
    simpa only [d1127, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7604 (pattern : Twelve) (guard : d1867 pattern = 1) : d1145 pattern ≤ (0 : Int) + d1210 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1145, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1145, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1145, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7603 pattern childGuard
    simpa only [d1145, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7605 (pattern : Twelve) (guard : d1867 pattern = 1) : d1160 pattern ≤ (0 : Int) + d1224 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1160, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7592 pattern childGuard
    simpa only [d1160, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1160, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7604 pattern childGuard
    simpa only [d1160, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7606 (pattern : Twelve) (guard : d1867 pattern = 1) : d1115 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1115, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1115, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1115, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7579 pattern childGuard
    simpa only [d1115, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7607 (pattern : Twelve) (guard : d1867 pattern = 1) : d1128 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1128, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7606 pattern childGuard
    simpa only [d1128, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1128, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7560 pattern childGuard
    simpa only [d1128, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7608 (pattern : Twelve) (guard : d1867 pattern = 1) : d1146 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1146, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1146, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1146, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7607 pattern childGuard
    simpa only [d1146, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7609 (pattern : Twelve) (guard : d1867 pattern = 1) : d1147 pattern ≤ (0 : Int) + d1211 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1147, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1147, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1147, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7603 pattern childGuard
    simpa only [d1147, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7610 (pattern : Twelve) (guard : d1867 pattern = 1) : d1161 pattern ≤ (0 : Int) + d1225 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1161, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7608 pattern childGuard
    simpa only [d1161, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1161, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7609 pattern childGuard
    simpa only [d1161, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7611 (pattern : Twelve) (guard : d1867 pattern = 1) : d1170 pattern ≤ (0 : Int) + d1234 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1170, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7605 pattern childGuard
    simpa only [d1170, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1170, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7610 pattern childGuard
    simpa only [d1170, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7612 (pattern : Twelve) (guard : d1867 pattern = 1) : d1116 pattern ≤ (0 : Int) + d1188 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1116, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1116, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1116, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7468 pattern childGuard
    simpa only [d1116, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7613 (pattern : Twelve) (guard : d1867 pattern = 1) : d1129 pattern ≤ (0 : Int) + d1197 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1129, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7606 pattern childGuard
    simpa only [d1129, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1129, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7612 pattern childGuard
    simpa only [d1129, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7614 (pattern : Twelve) (guard : d1867 pattern = 1) : d1148 pattern ≤ (0 : Int) + d1212 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7613 pattern childGuard
    simpa only [d1148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7615 (pattern : Twelve) (guard : d1867 pattern = 1) : d1149 pattern ≤ (0 : Int) + d1213 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1149, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7508 pattern childGuard
    simpa only [d1149, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1149, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7603 pattern childGuard
    simpa only [d1149, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7616 (pattern : Twelve) (guard : d1867 pattern = 1) : d1162 pattern ≤ (0 : Int) + d1226 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1162, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7614 pattern childGuard
    simpa only [d1162, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1162, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7615 pattern childGuard
    simpa only [d1162, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7617 (pattern : Twelve) (guard : d1867 pattern = 1) : d1107 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1107, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d1867, d1107, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1107, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7014 pattern childGuard
    simpa only [d1867, d1107, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7618 (pattern : Twelve) (guard : d1867 pattern = 1) : d1117 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1117, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7617 pattern childGuard
    simpa only [d1117, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1117, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1117, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7619 (pattern : Twelve) (guard : d1867 pattern = 1) : d1130 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1130, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7540 pattern childGuard
    simpa only [d1130, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1130, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7618 pattern childGuard
    simpa only [d1130, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7620 (pattern : Twelve) (guard : d1867 pattern = 1) : d1150 pattern ≤ (0 : Int) + d1214 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1150, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d1150, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1150, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7619 pattern childGuard
    simpa only [d1150, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7621 (pattern : Twelve) (guard : d1867 pattern = 1) : d1131 pattern ≤ (0 : Int) + d1198 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1131, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7476 pattern childGuard
    simpa only [d1131, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1131, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1131, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7622 (pattern : Twelve) (guard : d1867 pattern = 1) : d1151 pattern ≤ (0 : Int) + d1215 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1151, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7538 pattern childGuard
    simpa only [d1151, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1151, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7621 pattern childGuard
    simpa only [d1151, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7623 (pattern : Twelve) (guard : d1867 pattern = 1) : d1163 pattern ≤ (0 : Int) + d1227 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1163, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7620 pattern childGuard
    simpa only [d1163, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1163, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7622 pattern childGuard
    simpa only [d1163, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7624 (pattern : Twelve) (guard : d1867 pattern = 1) : d1171 pattern ≤ (0 : Int) + d1235 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1171, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7616 pattern childGuard
    simpa only [d1171, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1171, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7623 pattern childGuard
    simpa only [d1171, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7625 (pattern : Twelve) (guard : d1867 pattern = 1) : d1172 pattern ≤ (0 : Int) + d1236 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1172, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7610 pattern childGuard
    simpa only [d1172, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1172, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1172, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7626 (pattern : Twelve) (guard : d1867 pattern = 1) : d1176 pattern ≤ (0 : Int) + d1240 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1176, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7624 pattern childGuard
    simpa only [d1176, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1176, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7625 pattern childGuard
    simpa only [d1176, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7627 (pattern : Twelve) (guard : d1867 pattern = 1) : d1179 pattern ≤ (0 : Int) + d1243 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1179, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7611 pattern childGuard
    simpa only [d1179, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1179, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7626 pattern childGuard
    simpa only [d1179, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7628 (pattern : Twelve) (guard : d1867 pattern = 1) : d1182 pattern ≤ (0 : Int) + d1246 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1182, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7601 pattern childGuard
    simpa only [d1182, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1182, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7627 pattern childGuard
    simpa only [d1182, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7629 (pattern : Twelve) (guard : d1867 pattern = 1) : d1505 pattern ≤ (0 : Int) + d1564 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1505, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7551 pattern childGuard
    simpa only [d1505, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1505, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1505, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7630 (pattern : Twelve) (guard : d1867 pattern = 1) : d1517 pattern ≤ (0 : Int) + d1576 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1517, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7554 pattern childGuard
    simpa only [d1517, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1517, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7629 pattern childGuard
    simpa only [d1517, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7631 (pattern : Twelve) (guard : d1867 pattern = 1) : d1518 pattern ≤ (0 : Int) + d1577 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1518, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1518, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1518, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1518, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7632 (pattern : Twelve) (guard : d1867 pattern = 1) : d1532 pattern ≤ (0 : Int) + d1591 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1532, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7630 pattern childGuard
    simpa only [d1532, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1532, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7631 pattern childGuard
    simpa only [d1532, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7633 (pattern : Twelve) (guard : d1867 pattern = 1) : d1495 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1495, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1495, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1495, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7579 pattern childGuard
    simpa only [d1495, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7634 (pattern : Twelve) (guard : d1867 pattern = 1) : d1496 pattern ≤ (0 : Int) + d1557 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1496, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1496, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1496, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1496, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7635 (pattern : Twelve) (guard : d1867 pattern = 1) : d1506 pattern ≤ (0 : Int) + d1565 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1506, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7633 pattern childGuard
    simpa only [d1506, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1506, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7634 pattern childGuard
    simpa only [d1506, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7636 (pattern : Twelve) (guard : d1867 pattern = 1) : d1519 pattern ≤ (0 : Int) + d1578 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1519, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1519, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1519, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7635 pattern childGuard
    simpa only [d1519, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7637 (pattern : Twelve) (guard : d1867 pattern = 1) : d1507 pattern ≤ (0 : Int) + d1566 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1507, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1507, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1507, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7401 pattern childGuard
    simpa only [d1507, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7638 (pattern : Twelve) (guard : d1867 pattern = 1) : d1520 pattern ≤ (0 : Int) + d1579 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1520, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7637 pattern childGuard
    simpa only [d1520, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1520, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1520, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7639 (pattern : Twelve) (guard : d1867 pattern = 1) : d1533 pattern ≤ (0 : Int) + d1592 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1533, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7636 pattern childGuard
    simpa only [d1533, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1533, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7638 pattern childGuard
    simpa only [d1533, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7640 (pattern : Twelve) (guard : d1867 pattern = 1) : d1541 pattern ≤ (0 : Int) + d1600 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1541, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7632 pattern childGuard
    simpa only [d1541, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1541, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7639 pattern childGuard
    simpa only [d1541, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7641 (pattern : Twelve) (guard : d1867 pattern = 1) : d1521 pattern ≤ (0 : Int) + d1580 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1521, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1521, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1521, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7629 pattern childGuard
    simpa only [d1521, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7642 (pattern : Twelve) (guard : d1867 pattern = 1) : d1534 pattern ≤ (0 : Int) + d1593 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1534, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7641 pattern childGuard
    simpa only [d1534, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1534, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7631 pattern childGuard
    simpa only [d1534, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7643 (pattern : Twelve) (guard : d1867 pattern = 1) : d1542 pattern ≤ (0 : Int) + d1601 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1542, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7642 pattern childGuard
    simpa only [d1542, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1542, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7639 pattern childGuard
    simpa only [d1542, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7644 (pattern : Twelve) (guard : d1867 pattern = 1) : d1548 pattern ≤ (0 : Int) + d1607 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1548, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7640 pattern childGuard
    simpa only [d1548, d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1548, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7643 pattern childGuard
    simpa only [d1548, d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7645 (pattern : Twelve) (guard : d1867 pattern = 1) : d1497 pattern ≤ (0 : Int) + d1558 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1497, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1497, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1497, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7459 pattern childGuard
    simpa only [d1497, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7646 (pattern : Twelve) (guard : d1867 pattern = 1) : d1508 pattern ≤ (0 : Int) + d1567 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1508, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7633 pattern childGuard
    simpa only [d1508, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1508, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7645 pattern childGuard
    simpa only [d1508, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7647 (pattern : Twelve) (guard : d1867 pattern = 1) : d1522 pattern ≤ (0 : Int) + d1581 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1522, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1522, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1522, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7646 pattern childGuard
    simpa only [d1522, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7648 (pattern : Twelve) (guard : d1867 pattern = 1) : d1523 pattern ≤ (0 : Int) + d1582 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1523, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1523, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1523, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1523, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7649 (pattern : Twelve) (guard : d1867 pattern = 1) : d1535 pattern ≤ (0 : Int) + d1594 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1535, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7647 pattern childGuard
    simpa only [d1535, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1535, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7648 pattern childGuard
    simpa only [d1535, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7650 (pattern : Twelve) (guard : d1867 pattern = 1) : d1493 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1493, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d1867, d1493, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1493, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1867, d1493, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7651 (pattern : Twelve) (guard : d1867 pattern = 1) : d1498 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1498, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7579 pattern childGuard
    simpa only [d1498, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1498, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7650 pattern childGuard
    simpa only [d1498, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7652 (pattern : Twelve) (guard : d1867 pattern = 1) : d1509 pattern ≤ (0 : Int) + d1568 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1509, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7651 pattern childGuard
    simpa only [d1509, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1509, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7537 pattern childGuard
    simpa only [d1509, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7653 (pattern : Twelve) (guard : d1867 pattern = 1) : d1524 pattern ≤ (0 : Int) + d1583 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1524, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d1524, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1524, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7652 pattern childGuard
    simpa only [d1524, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7654 (pattern : Twelve) (guard : d1867 pattern = 1) : d1510 pattern ≤ (0 : Int) + d1569 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1510, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7583 pattern childGuard
    simpa only [d1510, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1510, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7476 pattern childGuard
    simpa only [d1510, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7655 (pattern : Twelve) (guard : d1867 pattern = 1) : d1525 pattern ≤ (0 : Int) + d1584 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1525, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7654 pattern childGuard
    simpa only [d1525, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1525, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1525, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7656 (pattern : Twelve) (guard : d1867 pattern = 1) : d1536 pattern ≤ (0 : Int) + d1595 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1536, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7653 pattern childGuard
    simpa only [d1536, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1536, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7655 pattern childGuard
    simpa only [d1536, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7657 (pattern : Twelve) (guard : d1867 pattern = 1) : d1543 pattern ≤ (0 : Int) + d1602 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1543, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7649 pattern childGuard
    simpa only [d1543, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1543, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7656 pattern childGuard
    simpa only [d1543, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7658 (pattern : Twelve) (guard : d1867 pattern = 1) : d1544 pattern ≤ (0 : Int) + d1603 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1544, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7639 pattern childGuard
    simpa only [d1544, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1544, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1544, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7659 (pattern : Twelve) (guard : d1867 pattern = 1) : d1549 pattern ≤ (0 : Int) + d1608 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1549, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7657 pattern childGuard
    simpa only [d1549, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1549, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7658 pattern childGuard
    simpa only [d1549, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7660 (pattern : Twelve) (guard : d1867 pattern = 1) : d1551 pattern ≤ (0 : Int) + d1610 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1551, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7644 pattern childGuard
    simpa only [d1551, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1551, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7659 pattern childGuard
    simpa only [d1551, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7661 (pattern : Twelve) (guard : d1867 pattern = 1) : d1552 pattern ≤ (0 : Int) + d1611 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1552, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7643 pattern childGuard
    simpa only [d1552, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1552, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7659 pattern childGuard
    simpa only [d1552, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7662 (pattern : Twelve) (guard : d1867 pattern = 1) : d1554 pattern ≤ (0 : Int) + d1613 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1554, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7660 pattern childGuard
    simpa only [d1554, d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1554, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7661 pattern childGuard
    simpa only [d1554, d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7663 (pattern : Twelve) (guard : d1867 pattern = 1) : d1555 pattern ≤ (0 : Int) + d1614 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1555, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7662 pattern childGuard
    simpa only [d1555, d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1555, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7661 pattern childGuard
    simpa only [d1555, d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7664 (pattern : Twelve) (guard : d1867 pattern = 1) : d1494 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1494, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3602 pattern childGuard
    simpa only [d1867, d1494, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1494, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7397 pattern childGuard
    simpa only [d1867, d1494, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7665 (pattern : Twelve) (guard : d1867 pattern = 1) : d1499 pattern ≤ (0 : Int) + d1559 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1499, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1499, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1499, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1499, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7666 (pattern : Twelve) (guard : d1867 pattern = 1) : d1500 pattern ≤ (0 : Int) + d1560 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1500, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1500, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1500, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1500, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7667 (pattern : Twelve) (guard : d1867 pattern = 1) : d1511 pattern ≤ (0 : Int) + d1570 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1511, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7665 pattern childGuard
    simpa only [d1511, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1511, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7666 pattern childGuard
    simpa only [d1511, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7668 (pattern : Twelve) (guard : d1867 pattern = 1) : d1526 pattern ≤ (0 : Int) + d1585 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1526, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1526, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1526, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7667 pattern childGuard
    simpa only [d1526, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7669 (pattern : Twelve) (guard : d1867 pattern = 1) : d1537 pattern ≤ (0 : Int) + d1596 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1537, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7668 pattern childGuard
    simpa only [d1537, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1537, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7631 pattern childGuard
    simpa only [d1537, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7670 (pattern : Twelve) (guard : d1867 pattern = 1) : d1512 pattern ≤ (0 : Int) + d1571 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1512, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7574 pattern childGuard
    simpa only [d1512, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1512, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7634 pattern childGuard
    simpa only [d1512, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7671 (pattern : Twelve) (guard : d1867 pattern = 1) : d1527 pattern ≤ (0 : Int) + d1586 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1527, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d1527, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1527, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7670 pattern childGuard
    simpa only [d1527, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7672 (pattern : Twelve) (guard : d1867 pattern = 1) : d1538 pattern ≤ (0 : Int) + d1597 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1538, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7671 pattern childGuard
    simpa only [d1538, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1538, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7638 pattern childGuard
    simpa only [d1538, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7673 (pattern : Twelve) (guard : d1867 pattern = 1) : d1545 pattern ≤ (0 : Int) + d1604 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1545, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7669 pattern childGuard
    simpa only [d1545, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1545, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7672 pattern childGuard
    simpa only [d1545, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7674 (pattern : Twelve) (guard : d1867 pattern = 1) : d1501 pattern ≤ (0 : Int) + d1561 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1501, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1501, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1501, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7650 pattern childGuard
    simpa only [d1501, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7675 (pattern : Twelve) (guard : d1867 pattern = 1) : d1513 pattern ≤ (0 : Int) + d1572 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1513, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7574 pattern childGuard
    simpa only [d1513, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1513, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7674 pattern childGuard
    simpa only [d1513, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7676 (pattern : Twelve) (guard : d1867 pattern = 1) : d1528 pattern ≤ (0 : Int) + d1587 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1528, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d1528, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1528, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7675 pattern childGuard
    simpa only [d1528, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7677 (pattern : Twelve) (guard : d1867 pattern = 1) : d1502 pattern ≤ (0 : Int) + d1562 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1502, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1502, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1502, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d1502, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7678 (pattern : Twelve) (guard : d1867 pattern = 1) : d1514 pattern ≤ (0 : Int) + d1573 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1514, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1514, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1514, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7677 pattern childGuard
    simpa only [d1514, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7679 (pattern : Twelve) (guard : d1867 pattern = 1) : d1529 pattern ≤ (0 : Int) + d1588 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1529, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7678 pattern childGuard
    simpa only [d1529, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1529, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1529, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7680 (pattern : Twelve) (guard : d1867 pattern = 1) : d1539 pattern ≤ (0 : Int) + d1598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1539, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7676 pattern childGuard
    simpa only [d1539, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1539, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7679 pattern childGuard
    simpa only [d1539, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7681 (pattern : Twelve) (guard : d1867 pattern = 1) : d1503 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1503, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7650 pattern childGuard
    simpa only [d1503, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1503, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1503, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7682 (pattern : Twelve) (guard : d1867 pattern = 1) : d1515 pattern ≤ (0 : Int) + d1574 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1515, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7580 pattern childGuard
    simpa only [d1515, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1515, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7681 pattern childGuard
    simpa only [d1515, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7683 (pattern : Twelve) (guard : d1867 pattern = 1) : d1530 pattern ≤ (0 : Int) + d1589 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1530, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d1530, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1530, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7682 pattern childGuard
    simpa only [d1530, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7684 (pattern : Twelve) (guard : d1867 pattern = 1) : d1504 pattern ≤ (0 : Int) + d1563 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1504, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d1504, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1504, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1504, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7685 (pattern : Twelve) (guard : d1867 pattern = 1) : d1516 pattern ≤ (0 : Int) + d1575 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1516, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7684 pattern childGuard
    simpa only [d1516, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1516, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7541 pattern childGuard
    simpa only [d1516, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7686 (pattern : Twelve) (guard : d1867 pattern = 1) : d1531 pattern ≤ (0 : Int) + d1590 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1531, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7685 pattern childGuard
    simpa only [d1531, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1531, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1531, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7687 (pattern : Twelve) (guard : d1867 pattern = 1) : d1540 pattern ≤ (0 : Int) + d1599 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1540, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7683 pattern childGuard
    simpa only [d1540, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1540, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7686 pattern childGuard
    simpa only [d1540, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7688 (pattern : Twelve) (guard : d1867 pattern = 1) : d1546 pattern ≤ (0 : Int) + d1605 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1546, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7680 pattern childGuard
    simpa only [d1546, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1546, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7687 pattern childGuard
    simpa only [d1546, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7689 (pattern : Twelve) (guard : d1867 pattern = 1) : d1547 pattern ≤ (0 : Int) + d1606 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1547, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7672 pattern childGuard
    simpa only [d1547, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1547, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1547, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7690 (pattern : Twelve) (guard : d1867 pattern = 1) : d1550 pattern ≤ (0 : Int) + d1609 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1550, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7688 pattern childGuard
    simpa only [d1550, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1550, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7689 pattern childGuard
    simpa only [d1550, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7691 (pattern : Twelve) (guard : d1867 pattern = 1) : d1553 pattern ≤ (0 : Int) + d1612 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1553, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7673 pattern childGuard
    simpa only [d1553, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1553, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7690 pattern childGuard
    simpa only [d1553, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7692 (pattern : Twelve) (guard : d1867 pattern = 1) : d1556 pattern ≤ (0 : Int) + d1615 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1556, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7663 pattern childGuard
    simpa only [d1556, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1556, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7691 pattern childGuard
    simpa only [d1556, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7693 (pattern : Twelve) (guard : d1867 pattern = 1) : d1753 pattern ≤ (0 : Int) + d1788 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1753, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1753, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1753, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1753, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7694 (pattern : Twelve) (guard : d1867 pattern = 1) : d1754 pattern ≤ (0 : Int) + d1789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1754, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d1754, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1754, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1754, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7695 (pattern : Twelve) (guard : d1867 pattern = 1) : d1763 pattern ≤ (0 : Int) + d1797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1763, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7693 pattern childGuard
    simpa only [d1763, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1763, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7694 pattern childGuard
    simpa only [d1763, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7696 (pattern : Twelve) (guard : d1867 pattern = 1) : d1745 pattern ≤ (0 : Int) + d1780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1745, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1745, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1745, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d1745, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7697 (pattern : Twelve) (guard : d1867 pattern = 1) : d1746 pattern ≤ (0 : Int) + d1781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1746, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7664 pattern childGuard
    simpa only [d1746, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1746, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1746, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7698 (pattern : Twelve) (guard : d1867 pattern = 1) : d1749 pattern ≤ (0 : Int) + d1784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1749, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7696 pattern childGuard
    simpa only [d1749, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1749, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7697 pattern childGuard
    simpa only [d1749, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7699 (pattern : Twelve) (guard : d1867 pattern = 1) : d1755 pattern ≤ (0 : Int) + d1790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1755, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7637 pattern childGuard
    simpa only [d1755, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1755, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7698 pattern childGuard
    simpa only [d1755, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
