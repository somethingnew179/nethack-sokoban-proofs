/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons06
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1120 (pattern : Ten) (guard : d384 pattern = 1) : d148 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d148, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1119 pattern childGuard
    simpa only [d148, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d148, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c477 pattern childGuard
    simpa only [d148, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1121 (pattern : Ten) (guard : d384 pattern = 1) : d149 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d149, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1120 pattern childGuard
    simpa only [d149, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d149, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c479 pattern childGuard
    simpa only [d149, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1122 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c481 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1123 (pattern : Ten) (guard : d383 pattern = 1) : d302 pattern ≤ (0 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d302, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1122 pattern childGuard
    simpa only [d302, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d302, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c483 pattern childGuard
    simpa only [d302, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1124 (pattern : Ten) (guard : d383 pattern = 1) : d304 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d304, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1123 pattern childGuard
    simpa only [d304, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d304, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c485 pattern childGuard
    simpa only [d304, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1125 (pattern : Ten) (guard : d383 pattern = 1) : d301 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d301, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d301, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d301, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c489 pattern childGuard
    simpa only [d301, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1126 (pattern : Ten) (guard : d383 pattern = 1) : d303 pattern ≤ (0 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d303, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1125 pattern childGuard
    simpa only [d303, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d303, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c491 pattern childGuard
    simpa only [d303, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1127 (pattern : Ten) (guard : d383 pattern = 1) : d305 pattern ≤ (0 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d305, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1126 pattern childGuard
    simpa only [d305, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d305, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c485 pattern childGuard
    simpa only [d305, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1128 (pattern : Ten) (guard : d383 pattern = 1) : d306 pattern ≤ (0 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d306, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1124 pattern childGuard
    simpa only [d306, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d306, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1127 pattern childGuard
    simpa only [d306, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1129 (pattern : Ten) (guard : d383 pattern = 1) : d307 pattern ≤ (0 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d307, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1128 pattern childGuard
    simpa only [d307, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d307, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d307, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1130 (pattern : Ten) (guard : d383 pattern = 1) : d308 pattern ≤ (0 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d308, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1129 pattern childGuard
    simpa only [d308, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d308, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c497 pattern childGuard
    simpa only [d308, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1131 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1132 (pattern : Ten) (guard : d395 pattern = 1) : d150 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1131 pattern childGuard
    simpa only [d395, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1133 (pattern : Ten) (guard : d395 pattern = 1) : d151 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1132 pattern childGuard
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c884 pattern childGuard
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1134 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1135 (pattern : Ten) (guard : d397 pattern = 1) : d154 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d154, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1133 pattern childGuard
    simpa only [d397, d154, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d154, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1134 pattern childGuard
    simpa only [d397, d154, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1136 (pattern : Ten) (guard : d0 pattern = 1) : d153 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1137 (pattern : Ten) (guard : d397 pattern = 1) : d155 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1136 pattern childGuard
    simpa only [d397, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1138 (pattern : Ten) (guard : d397 pattern = 1) : d156 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d397 pattern = 1 := by simpa only [d156, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1135 pattern childGuard
    simpa only [d156, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d397 pattern = 1 := by simpa only [d156, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1137 pattern childGuard
    simpa only [d156, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1139 (pattern : Ten) (guard : d394 pattern = 1) : d211 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d394, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1140 (pattern : Ten) (guard : d394 pattern = 1) : d326 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1139 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c891 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1141 (pattern : Ten) (guard : d0 pattern = 1) : d327 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1142 (pattern : Ten) (guard : d400 pattern = 1) : d329 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d329, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1140 pattern childGuard
    simpa only [d400, d329, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d329, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1141 pattern childGuard
    simpa only [d400, d329, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1143 (pattern : Ten) (guard : d0 pattern = 1) : d328 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1144 (pattern : Ten) (guard : d400 pattern = 1) : d330 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c925 pattern childGuard
    simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1143 pattern childGuard
    simpa only [d400, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1145 (pattern : Ten) (guard : d400 pattern = 1) : d331 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d400 pattern = 1 := by simpa only [d331, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1142 pattern childGuard
    simpa only [d331, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d400 pattern = 1 := by simpa only [d331, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1144 pattern childGuard
    simpa only [d331, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1146 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1147 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1146 pattern childGuard
    simpa only [d395, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1148 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1149 (pattern : Ten) (guard : d395 pattern = 1) : d55 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1148 pattern childGuard
    simpa only [d395, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1150 (pattern : Ten) (guard : d395 pattern = 1) : d152 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d152, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1147 pattern childGuard
    simpa only [d152, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d152, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d152, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1151 (pattern : Ten) (guard : d395 pattern = 1) : d154 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1133 pattern childGuard
    simpa only [d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1150 pattern childGuard
    simpa only [d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1152 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1153 (pattern : Ten) (guard : d395 pattern = 1) : d56 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1152 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1154 (pattern : Ten) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1155 (pattern : Ten) (guard : d395 pattern = 1) : d57 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1008 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1154 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1156 (pattern : Ten) (guard : d395 pattern = 1) : d153 pattern ≤ (0 : Int) + d63 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d153, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d153, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d153, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1155 pattern childGuard
    simpa only [d153, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1157 (pattern : Ten) (guard : d395 pattern = 1) : d155 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d155, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d155, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d155, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1156 pattern childGuard
    simpa only [d155, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1158 (pattern : Ten) (guard : d395 pattern = 1) : d156 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d156, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1151 pattern childGuard
    simpa only [d156, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d156, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1157 pattern childGuard
    simpa only [d156, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1159 (pattern : Ten) (guard : d394 pattern = 1) : d211 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d211, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d211, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d211, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1017 pattern childGuard
    simpa only [d394, d211, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1160 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1161 (pattern : Ten) (guard : d394 pattern = 1) : d207 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1160 pattern childGuard
    simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1162 (pattern : Ten) (guard : d394 pattern = 1) : d326 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1159 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1161 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1163 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (0 : Int) + d324 pattern := by
  omega
theorem c1164 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1165 (pattern : Ten) (guard : d394 pattern = 1) : d324 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1163 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1164 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1166 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (0 : Int) + d325 pattern := by
  omega
theorem c1167 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1168 (pattern : Ten) (guard : d394 pattern = 1) : d325 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1166 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1167 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1169 (pattern : Ten) (guard : d394 pattern = 1) : d327 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d327, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1165 pattern childGuard
    simpa only [d327, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d327, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1168 pattern childGuard
    simpa only [d327, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1170 (pattern : Ten) (guard : d394 pattern = 1) : d329 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d329, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1162 pattern childGuard
    simpa only [d329, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d329, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1169 pattern childGuard
    simpa only [d329, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1171 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d210 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1172 (pattern : Ten) (guard : d394 pattern = 1) : d209 pattern ≤ (0 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1171 pattern childGuard
    simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1173 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (0 : Int) + d210 pattern := by
  omega
theorem c1174 (pattern : Ten) (guard : d0 pattern = 1) : d210 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1175 (pattern : Ten) (guard : d394 pattern = 1) : d210 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1173 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1174 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1176 (pattern : Ten) (guard : d394 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c1177 (pattern : Ten) (guard : d394 pattern = 1) : d328 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d328, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1175 pattern childGuard
    simpa only [d328, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d328, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1176 pattern childGuard
    simpa only [d328, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1178 (pattern : Ten) (guard : d394 pattern = 1) : d330 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d330, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1172 pattern childGuard
    simpa only [d330, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d330, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1177 pattern childGuard
    simpa only [d330, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1179 (pattern : Ten) (guard : d394 pattern = 1) : d331 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d331, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1170 pattern childGuard
    simpa only [d331, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d331, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1178 pattern childGuard
    simpa only [d331, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1180 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1181 (pattern : Ten) (guard : d395 pattern = 1) : d150 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d150, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d150, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d150, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1180 pattern childGuard
    simpa only [d395, d150, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1182 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1183 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d161 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1182 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1184 (pattern : Ten) (guard : d395 pattern = 1) : d151 pattern ≤ (0 : Int) + d165 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1181 pattern childGuard
    simpa only [d151, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d151, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1183 pattern childGuard
    simpa only [d151, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1185 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1186 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1185 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1187 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1188 (pattern : Ten) (guard : d395 pattern = 1) : d55 pattern ≤ (0 : Int) + d163 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1187 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1189 (pattern : Ten) (guard : d395 pattern = 1) : d152 pattern ≤ (0 : Int) + d166 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d152, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1186 pattern childGuard
    simpa only [d152, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d152, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1188 pattern childGuard
    simpa only [d152, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1190 (pattern : Ten) (guard : d395 pattern = 1) : d154 pattern ≤ (0 : Int) + d168 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d154, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1184 pattern childGuard
    simpa only [d154, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d154, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1189 pattern childGuard
    simpa only [d154, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1191 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1192 (pattern : Ten) (guard : d395 pattern = 1) : d56 pattern ≤ (0 : Int) + d164 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1191 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1193 (pattern : Ten) (guard : d395 pattern = 1) : d56 pattern ≤ (0 : Int) + d167 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1192 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1194 (pattern : Ten) (guard : d395 pattern = 1) : d155 pattern ≤ (0 : Int) + d169 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d155, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d155, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d155, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1156 pattern childGuard
    simpa only [d155, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1195 (pattern : Ten) (guard : d395 pattern = 1) : d156 pattern ≤ (0 : Int) + d170 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d156, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1190 pattern childGuard
    simpa only [d156, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d156, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1194 pattern childGuard
    simpa only [d156, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1196 (pattern : Ten) (guard : d394 pattern = 1) : d211 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d211, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d211, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d211, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1019 pattern childGuard
    simpa only [d394, d211, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1197 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d343 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1198 (pattern : Ten) (guard : d394 pattern = 1) : d207 pattern ≤ (0 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1197 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1199 (pattern : Ten) (guard : d394 pattern = 1) : d326 pattern ≤ (0 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1196 pattern childGuard
    simpa only [d326, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1198 pattern childGuard
    simpa only [d326, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1200 (pattern : Ten) (guard : d394 pattern = 1) : d329 pattern ≤ (0 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d329, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1199 pattern childGuard
    simpa only [d329, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d329, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1169 pattern childGuard
    simpa only [d329, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1201 (pattern : Ten) (guard : d394 pattern = 1) : d209 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c932 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1202 (pattern : Ten) (guard : d394 pattern = 1) : d330 pattern ≤ (0 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d330, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1201 pattern childGuard
    simpa only [d330, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d330, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1177 pattern childGuard
    simpa only [d330, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1203 (pattern : Ten) (guard : d394 pattern = 1) : d331 pattern ≤ (0 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d331, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1200 pattern childGuard
    simpa only [d331, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d331, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1202 pattern childGuard
    simpa only [d331, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1204 (pattern : Ten) (guard : d395 pattern = 1) : d211 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d211, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c299 pattern childGuard
    simpa only [d395, d211, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d211, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d395, d211, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1205 (pattern : Ten) (guard : d395 pattern = 1) : d326 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d326, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1204 pattern childGuard
    simpa only [d326, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d326, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1015 pattern childGuard
    simpa only [d326, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1206 (pattern : Ten) (guard : d0 pattern = 1) : d309 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1207 (pattern : Ten) (guard : d350 pattern = 1) : d313 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1206 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1208 (pattern : Ten) (guard : d0 pattern = 1) : d310 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1209 (pattern : Ten) (guard : d350 pattern = 1) : d314 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1208 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1210 (pattern : Ten) (guard : d350 pattern = 1) : d317 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1207 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1209 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1211 (pattern : Ten) (guard : d0 pattern = 1) : d311 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1212 (pattern : Ten) (guard : d350 pattern = 1) : d315 pattern ≤ (0 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c949 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1211 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1213 (pattern : Ten) (guard : d350 pattern = 1) : d318 pattern ≤ (0 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1212 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1214 (pattern : Ten) (guard : d350 pattern = 1) : d321 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1210 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1213 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1215 (pattern : Ten) (guard : d0 pattern = 1) : d312 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1216 (pattern : Ten) (guard : d350 pattern = 1) : d316 pattern ≤ (0 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c954 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1215 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1217 (pattern : Ten) (guard : d350 pattern = 1) : d319 pattern ≤ (0 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1216 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1218 (pattern : Ten) (guard : d350 pattern = 1) : d322 pattern ≤ (0 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1217 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1219 (pattern : Ten) (guard : d350 pattern = 1) : d324 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1214 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1218 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1220 (pattern : Ten) (guard : d395 pattern = 1) : d324 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1164 pattern childGuard
    simpa only [d395, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1221 (pattern : Ten) (guard : d350 pattern = 1) : d320 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1209 pattern childGuard
    simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1212 pattern childGuard
    simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1222 (pattern : Ten) (guard : d350 pattern = 1) : d323 pattern ≤ (0 : Int) + d204 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1221 pattern childGuard
    simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1217 pattern childGuard
    simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1223 (pattern : Ten) (guard : d350 pattern = 1) : d325 pattern ≤ (0 : Int) + d208 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1222 pattern childGuard
    simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c324 pattern childGuard
    simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1224 (pattern : Ten) (guard : d395 pattern = 1) : d325 pattern ≤ (0 : Int) + d212 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1223 pattern childGuard
    simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1167 pattern childGuard
    simpa only [d395, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1225 (pattern : Ten) (guard : d395 pattern = 1) : d327 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d327, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1220 pattern childGuard
    simpa only [d327, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d327, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1224 pattern childGuard
    simpa only [d327, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1226 (pattern : Ten) (guard : d395 pattern = 1) : d329 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d329, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1205 pattern childGuard
    simpa only [d329, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d329, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1225 pattern childGuard
    simpa only [d329, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1227 (pattern : Ten) (guard : d395 pattern = 1) : d210 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1174 pattern childGuard
    simpa only [d395, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1228 (pattern : Ten) (guard : d395 pattern = 1) : d328 pattern ≤ (0 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d328, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1227 pattern childGuard
    simpa only [d328, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d328, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1026 pattern childGuard
    simpa only [d328, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1229 (pattern : Ten) (guard : d395 pattern = 1) : d330 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d330, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1023 pattern childGuard
    simpa only [d330, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d330, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1228 pattern childGuard
    simpa only [d330, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1230 (pattern : Ten) (guard : d395 pattern = 1) : d331 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d331, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1226 pattern childGuard
    simpa only [d331, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d331, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1229 pattern childGuard
    simpa only [d331, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1231 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1232 (pattern : Ten) (guard : d397 pattern = 1) : d154 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d397, d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1133 pattern childGuard
    simpa only [d397, d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d397, d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1231 pattern childGuard
    simpa only [d397, d154, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1233 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1234 (pattern : Ten) (guard : d398 pattern = 1) : d156 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d397 pattern = 1 := by simpa only [d398, d156, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1232 pattern childGuard
    simpa only [d398, d156, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d398, d156, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1233 pattern childGuard
    simpa only [d398, d156, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1235 (pattern : Ten) (guard : d0 pattern = 1) : d327 pattern ≤ (0 : Int) + d215 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1236 (pattern : Ten) (guard : d400 pattern = 1) : d329 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d400, d329, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1140 pattern childGuard
    simpa only [d400, d329, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d400, d329, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1235 pattern childGuard
    simpa only [d400, d329, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1237 (pattern : Ten) (guard : d0 pattern = 1) : d330 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1238 (pattern : Ten) (guard : d401 pattern = 1) : d331 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d400 pattern = 1 := by simpa only [d401, d331, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1236 pattern childGuard
    simpa only [d401, d331, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d401, d331, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1237 pattern childGuard
    simpa only [d401, d331, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1239 (pattern : Ten) (guard : d350 pattern = 1) : d332 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c299 pattern childGuard
    simpa only [d332, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d332, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1240 (pattern : Ten) (guard : d350 pattern = 1) : d332 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1241 (pattern : Ten) (guard : d350 pattern = 1) : d332 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1239 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1240 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1242 (pattern : Ten) (guard : d350 pattern = 1) : d333 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1243 (pattern : Ten) (guard : d350 pattern = 1) : d334 pattern ≤ (0 : Int) + d212 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1223 pattern childGuard
    simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1244 (pattern : Ten) (guard : d350 pattern = 1) : d336 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1242 pattern childGuard
    simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1243 pattern childGuard
    simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1245 (pattern : Ten) (guard : d350 pattern = 1) : d338 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d338, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1241 pattern childGuard
    simpa only [d338, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d338, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1244 pattern childGuard
    simpa only [d338, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1246 (pattern : Ten) (guard : d350 pattern = 1) : d335 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1247 (pattern : Ten) (guard : d350 pattern = 1) : d337 pattern ≤ (0 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1246 pattern childGuard
    simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1248 (pattern : Ten) (guard : d350 pattern = 1) : d339 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c326 pattern childGuard
    simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1247 pattern childGuard
    simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1249 (pattern : Ten) (guard : d350 pattern = 1) : d340 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d340, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1245 pattern childGuard
    simpa only [d340, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d340, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1248 pattern childGuard
    simpa only [d340, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1250 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d332, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d332, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d332, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1164 pattern childGuard
    simpa only [d394, d332, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1251 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1252 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1251 pattern childGuard
    simpa only [d394, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1253 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1250 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1252 pattern childGuard
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1254 (pattern : Ten) (guard : d394 pattern = 1) : d333 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1163 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1017 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1255 (pattern : Ten) (guard : d394 pattern = 1) : d334 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1166 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1019 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1256 (pattern : Ten) (guard : d394 pattern = 1) : d336 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d336, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1254 pattern childGuard
    simpa only [d336, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d336, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1255 pattern childGuard
    simpa only [d336, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1257 (pattern : Ten) (guard : d394 pattern = 1) : d338 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d338, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1253 pattern childGuard
    simpa only [d338, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d338, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1256 pattern childGuard
    simpa only [d338, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1258 (pattern : Ten) (guard : d0 pattern = 1) : d210 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1259 (pattern : Ten) (guard : d394 pattern = 1) : d213 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1258 pattern childGuard
    simpa only [d394, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1260 (pattern : Ten) (guard : d394 pattern = 1) : d335 pattern ≤ (0 : Int) + d210 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1173 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1024 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1261 (pattern : Ten) (guard : d394 pattern = 1) : d337 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d337, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1260 pattern childGuard
    simpa only [d337, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d337, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1176 pattern childGuard
    simpa only [d337, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1262 (pattern : Ten) (guard : d394 pattern = 1) : d339 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d339, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1259 pattern childGuard
    simpa only [d339, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d339, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1261 pattern childGuard
    simpa only [d339, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1263 (pattern : Ten) (guard : d394 pattern = 1) : d340 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d340, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1257 pattern childGuard
    simpa only [d340, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d340, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1262 pattern childGuard
    simpa only [d340, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1264 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1265 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1264 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1266 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (0 : Int) + d165 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1265 pattern childGuard
    simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1183 pattern childGuard
    simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1267 (pattern : Ten) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1268 (pattern : Ten) (guard : d395 pattern = 1) : d58 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d58, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d58, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d58, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d395, d58, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1269 (pattern : Ten) (guard : d395 pattern = 1) : d59 pattern ≤ (0 : Int) + d163 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d59, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d59, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d59, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d395, d59, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1270 (pattern : Ten) (guard : d395 pattern = 1) : d62 pattern ≤ (0 : Int) + d166 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d62, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1268 pattern childGuard
    simpa only [d62, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d62, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1269 pattern childGuard
    simpa only [d62, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1271 (pattern : Ten) (guard : d395 pattern = 1) : d64 pattern ≤ (0 : Int) + d168 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d64, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1266 pattern childGuard
    simpa only [d64, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d64, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1270 pattern childGuard
    simpa only [d64, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1272 (pattern : Ten) (guard : d395 pattern = 1) : d63 pattern ≤ (0 : Int) + d63 pattern := by
  omega
theorem c1273 (pattern : Ten) (guard : d395 pattern = 1) : d65 pattern ≤ (0 : Int) + d169 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d65, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d65, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d65, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1272 pattern childGuard
    simpa only [d65, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1274 (pattern : Ten) (guard : d395 pattern = 1) : d66 pattern ≤ (0 : Int) + d170 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1271 pattern childGuard
    simpa only [d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1273 pattern childGuard
    simpa only [d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1275 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d325 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1276 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d332, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d332, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d332, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1275 pattern childGuard
    simpa only [d394, d332, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1277 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d343 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1278 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d332, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d332, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d332, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1277 pattern childGuard
    simpa only [d394, d332, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1279 (pattern : Ten) (guard : d394 pattern = 1) : d332 pattern ≤ (0 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1276 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1278 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
