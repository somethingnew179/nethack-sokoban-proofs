/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons007
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1120 (pattern : Twelve) (guard : d1837 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1698, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1116 pattern childGuard
    simpa only [d1698, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1698, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1119 pattern childGuard
    simpa only [d1698, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1121 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d128 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1122 (pattern : Twelve) (guard : d1837 pattern = 1) : d1692 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1692, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d1837, d1692, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1692, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1837, d1692, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1123 (pattern : Twelve) (guard : d1837 pattern = 1) : d1696 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1696, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1071 pattern childGuard
    simpa only [d1696, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1696, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1122 pattern childGuard
    simpa only [d1696, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1124 (pattern : Twelve) (guard : d1837 pattern = 1) : d1252 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c414 pattern childGuard
    simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c999 pattern childGuard
    simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1125 (pattern : Twelve) (guard : d1837 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1124 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1126 (pattern : Twelve) (guard : d1837 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1699, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1123 pattern childGuard
    simpa only [d1699, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1699, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1125 pattern childGuard
    simpa only [d1699, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1127 (pattern : Twelve) (guard : d1837 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1701, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1120 pattern childGuard
    simpa only [d1701, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1701, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1126 pattern childGuard
    simpa only [d1701, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1128 (pattern : Twelve) (guard : d1837 pattern = 1) : d1702 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1702, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1112 pattern childGuard
    simpa only [d1702, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1702, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1702, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1129 (pattern : Twelve) (guard : d1837 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1703, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1127 pattern childGuard
    simpa only [d1703, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1703, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1128 pattern childGuard
    simpa only [d1703, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1130 (pattern : Twelve) (guard : d1837 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1704, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1113 pattern childGuard
    simpa only [d1704, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1704, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1129 pattern childGuard
    simpa only [d1704, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1131 (pattern : Twelve) (guard : d0 pattern = 1) : d257 pattern ≤ (0 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1132 (pattern : Twelve) (guard : d1847 pattern = 1) : d272 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d272, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c814 pattern childGuard
    simpa only [d1847, d272, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d272, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1131 pattern childGuard
    simpa only [d1847, d272, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1133 (pattern : Twelve) (guard : d0 pattern = 1) : d259 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1134 (pattern : Twelve) (guard : d1847 pattern = 1) : d273 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d273, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c825 pattern childGuard
    simpa only [d1847, d273, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d273, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1133 pattern childGuard
    simpa only [d1847, d273, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1135 (pattern : Twelve) (guard : d1847 pattern = 1) : d284 pattern ≤ (0 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d284, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1132 pattern childGuard
    simpa only [d284, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d284, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1134 pattern childGuard
    simpa only [d284, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1136 (pattern : Twelve) (guard : d0 pattern = 1) : d261 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1137 (pattern : Twelve) (guard : d1847 pattern = 1) : d274 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d274, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c837 pattern childGuard
    simpa only [d1847, d274, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d274, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1136 pattern childGuard
    simpa only [d1847, d274, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1138 (pattern : Twelve) (guard : d0 pattern = 1) : d263 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1139 (pattern : Twelve) (guard : d1847 pattern = 1) : d275 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d275, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c846 pattern childGuard
    simpa only [d1847, d275, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d275, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1138 pattern childGuard
    simpa only [d1847, d275, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1140 (pattern : Twelve) (guard : d1847 pattern = 1) : d285 pattern ≤ (0 : Int) + d321 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d285, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1137 pattern childGuard
    simpa only [d285, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d285, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1139 pattern childGuard
    simpa only [d285, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1141 (pattern : Twelve) (guard : d1847 pattern = 1) : d293 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d293, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1135 pattern childGuard
    simpa only [d293, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d293, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1140 pattern childGuard
    simpa only [d293, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1142 (pattern : Twelve) (guard : d0 pattern = 1) : d265 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1143 (pattern : Twelve) (guard : d1847 pattern = 1) : d276 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d276, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c857 pattern childGuard
    simpa only [d1847, d276, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d276, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1142 pattern childGuard
    simpa only [d1847, d276, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1144 (pattern : Twelve) (guard : d0 pattern = 1) : d267 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1145 (pattern : Twelve) (guard : d1847 pattern = 1) : d277 pattern ≤ (0 : Int) + d309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d277, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c866 pattern childGuard
    simpa only [d1847, d277, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d277, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1144 pattern childGuard
    simpa only [d1847, d277, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1146 (pattern : Twelve) (guard : d1847 pattern = 1) : d286 pattern ≤ (0 : Int) + d322 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d286, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1143 pattern childGuard
    simpa only [d286, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d286, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1145 pattern childGuard
    simpa only [d286, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1147 (pattern : Twelve) (guard : d0 pattern = 1) : d263 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1148 (pattern : Twelve) (guard : d1847 pattern = 1) : d278 pattern ≤ (0 : Int) + d310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d278, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c876 pattern childGuard
    simpa only [d1847, d278, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d278, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1147 pattern childGuard
    simpa only [d1847, d278, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1149 (pattern : Twelve) (guard : d1847 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c1150 (pattern : Twelve) (guard : d1847 pattern = 1) : d287 pattern ≤ (0 : Int) + d323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d287, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1148 pattern childGuard
    simpa only [d287, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d287, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d287, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1151 (pattern : Twelve) (guard : d1847 pattern = 1) : d294 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d294, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1146 pattern childGuard
    simpa only [d294, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d294, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1150 pattern childGuard
    simpa only [d294, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1152 (pattern : Twelve) (guard : d1847 pattern = 1) : d297 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d297, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1141 pattern childGuard
    simpa only [d297, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d297, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1151 pattern childGuard
    simpa only [d297, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1153 (pattern : Twelve) (guard : d0 pattern = 1) : d263 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1154 (pattern : Twelve) (guard : d1847 pattern = 1) : d279 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d279, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d1847, d279, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d279, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d279, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1155 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c894 pattern childGuard
    simpa only [d1847, d280, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1156 (pattern : Twelve) (guard : d1847 pattern = 1) : d288 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d288, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1154 pattern childGuard
    simpa only [d288, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d288, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1155 pattern childGuard
    simpa only [d288, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1157 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d313 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c903 pattern childGuard
    simpa only [d1847, d280, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1158 (pattern : Twelve) (guard : d1847 pattern = 1) : d288 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d288, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1154 pattern childGuard
    simpa only [d288, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d288, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1157 pattern childGuard
    simpa only [d288, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1159 (pattern : Twelve) (guard : d1847 pattern = 1) : d288 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1156 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1158 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1160 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c911 pattern childGuard
    simpa only [d1847, d280, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1161 (pattern : Twelve) (guard : d0 pattern = 1) : d267 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1162 (pattern : Twelve) (guard : d1847 pattern = 1) : d281 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d281, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c918 pattern childGuard
    simpa only [d1847, d281, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d281, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1161 pattern childGuard
    simpa only [d1847, d281, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1163 (pattern : Twelve) (guard : d1847 pattern = 1) : d289 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d289, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1160 pattern childGuard
    simpa only [d289, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d289, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1162 pattern childGuard
    simpa only [d289, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1164 (pattern : Twelve) (guard : d1847 pattern = 1) : d290 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d290, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1157 pattern childGuard
    simpa only [d290, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d290, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d290, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1165 (pattern : Twelve) (guard : d1847 pattern = 1) : d295 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d295, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1163 pattern childGuard
    simpa only [d295, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d295, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1164 pattern childGuard
    simpa only [d295, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1166 (pattern : Twelve) (guard : d1847 pattern = 1) : d298 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d298, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1159 pattern childGuard
    simpa only [d298, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d298, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1165 pattern childGuard
    simpa only [d298, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1167 (pattern : Twelve) (guard : d1847 pattern = 1) : d300 pattern ≤ (0 : Int) + d341 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d300, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1152 pattern childGuard
    simpa only [d300, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d300, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1166 pattern childGuard
    simpa only [d300, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1168 (pattern : Twelve) (guard : d0 pattern = 1) : d270 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1169 (pattern : Twelve) (guard : d1847 pattern = 1) : d282 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d282, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d1847, d282, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d282, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1168 pattern childGuard
    simpa only [d1847, d282, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1170 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c935 pattern childGuard
    simpa only [d1847, d280, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1171 (pattern : Twelve) (guard : d1847 pattern = 1) : d291 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d291, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1169 pattern childGuard
    simpa only [d291, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d291, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1170 pattern childGuard
    simpa only [d291, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1172 (pattern : Twelve) (guard : d0 pattern = 1) : d271 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1173 (pattern : Twelve) (guard : d1847 pattern = 1) : d283 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d283, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d1847, d283, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d283, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1172 pattern childGuard
    simpa only [d1847, d283, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1174 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d317 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c943 pattern childGuard
    simpa only [d1847, d280, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1175 (pattern : Twelve) (guard : d1847 pattern = 1) : d292 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d292, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1173 pattern childGuard
    simpa only [d292, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d292, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1174 pattern childGuard
    simpa only [d292, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1176 (pattern : Twelve) (guard : d1847 pattern = 1) : d296 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d296, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1171 pattern childGuard
    simpa only [d296, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d296, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1175 pattern childGuard
    simpa only [d296, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1177 (pattern : Twelve) (guard : d1847 pattern = 1) : d280 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c949 pattern childGuard
    simpa only [d1847, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1153 pattern childGuard
    simpa only [d1847, d280, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1178 (pattern : Twelve) (guard : d1847 pattern = 1) : d281 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c951 pattern childGuard
    simpa only [d1847, d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1161 pattern childGuard
    simpa only [d1847, d281, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1179 (pattern : Twelve) (guard : d1847 pattern = 1) : d289 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d289, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1177 pattern childGuard
    simpa only [d289, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d289, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1178 pattern childGuard
    simpa only [d289, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1180 (pattern : Twelve) (guard : d1847 pattern = 1) : d290 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d290, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1174 pattern childGuard
    simpa only [d290, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d290, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d290, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1181 (pattern : Twelve) (guard : d1847 pattern = 1) : d295 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d295, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1179 pattern childGuard
    simpa only [d295, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d295, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1180 pattern childGuard
    simpa only [d295, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1182 (pattern : Twelve) (guard : d1847 pattern = 1) : d299 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d299, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1176 pattern childGuard
    simpa only [d299, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d299, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1181 pattern childGuard
    simpa only [d299, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1183 (pattern : Twelve) (guard : d1847 pattern = 1) : d301 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d301, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1182 pattern childGuard
    simpa only [d301, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d301, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1166 pattern childGuard
    simpa only [d301, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1184 (pattern : Twelve) (guard : d1847 pattern = 1) : d302 pattern ≤ (0 : Int) + d343 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d302, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1167 pattern childGuard
    simpa only [d302, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d302, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1183 pattern childGuard
    simpa only [d302, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1185 (pattern : Twelve) (guard : d1847 pattern = 1) : d303 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d303, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1184 pattern childGuard
    simpa only [d303, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d303, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1183 pattern childGuard
    simpa only [d303, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1186 (pattern : Twelve) (guard : d0 pattern = 1) : d948 pattern ≤ (0 : Int) + d909 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1187 (pattern : Twelve) (guard : d1847 pattern = 1) : d955 pattern ≤ (0 : Int) + d980 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d955, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c962 pattern childGuard
    simpa only [d1847, d955, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d955, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1186 pattern childGuard
    simpa only [d1847, d955, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1188 (pattern : Twelve) (guard : d0 pattern = 1) : d949 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1189 (pattern : Twelve) (guard : d1847 pattern = 1) : d956 pattern ≤ (0 : Int) + d981 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d956, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c972 pattern childGuard
    simpa only [d1847, d956, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d956, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1188 pattern childGuard
    simpa only [d1847, d956, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1190 (pattern : Twelve) (guard : d1847 pattern = 1) : d963 pattern ≤ (0 : Int) + d991 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d963, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1187 pattern childGuard
    simpa only [d963, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d963, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1189 pattern childGuard
    simpa only [d963, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1191 (pattern : Twelve) (guard : d0 pattern = 1) : d951 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1192 (pattern : Twelve) (guard : d1847 pattern = 1) : d957 pattern ≤ (0 : Int) + d982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d957, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c979 pattern childGuard
    simpa only [d1847, d957, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d957, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1191 pattern childGuard
    simpa only [d1847, d957, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1193 (pattern : Twelve) (guard : d0 pattern = 1) : d949 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1194 (pattern : Twelve) (guard : d1847 pattern = 1) : d958 pattern ≤ (0 : Int) + d983 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d958, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c984 pattern childGuard
    simpa only [d1847, d958, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d958, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d1847, d958, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1195 (pattern : Twelve) (guard : d1847 pattern = 1) : d964 pattern ≤ (0 : Int) + d992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d964, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1192 pattern childGuard
    simpa only [d964, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d964, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1194 pattern childGuard
    simpa only [d964, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1196 (pattern : Twelve) (guard : d1847 pattern = 1) : d970 pattern ≤ (0 : Int) + d1000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d970, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1190 pattern childGuard
    simpa only [d970, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d970, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1195 pattern childGuard
    simpa only [d970, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1197 (pattern : Twelve) (guard : d0 pattern = 1) : d949 pattern ≤ (0 : Int) + d911 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1198 (pattern : Twelve) (guard : d1847 pattern = 1) : d959 pattern ≤ (0 : Int) + d984 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d959, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c990 pattern childGuard
    simpa only [d1847, d959, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d959, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1197 pattern childGuard
    simpa only [d1847, d959, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1199 (pattern : Twelve) (guard : d0 pattern = 1) : d952 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1200 (pattern : Twelve) (guard : d1847 pattern = 1) : d960 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d960, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c997 pattern childGuard
    simpa only [d1847, d960, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d960, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1199 pattern childGuard
    simpa only [d1847, d960, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1201 (pattern : Twelve) (guard : d1847 pattern = 1) : d965 pattern ≤ (0 : Int) + d993 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d965, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1198 pattern childGuard
    simpa only [d965, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d965, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1200 pattern childGuard
    simpa only [d965, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1202 (pattern : Twelve) (guard : d1847 pattern = 1) : d966 pattern ≤ (0 : Int) + d994 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d966, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1194 pattern childGuard
    simpa only [d966, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d966, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d966, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1203 (pattern : Twelve) (guard : d1847 pattern = 1) : d971 pattern ≤ (0 : Int) + d1001 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d971, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1201 pattern childGuard
    simpa only [d971, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d971, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1202 pattern childGuard
    simpa only [d971, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1204 (pattern : Twelve) (guard : d1847 pattern = 1) : d973 pattern ≤ (0 : Int) + d1004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d973, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1196 pattern childGuard
    simpa only [d973, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d973, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1203 pattern childGuard
    simpa only [d973, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1205 (pattern : Twelve) (guard : d0 pattern = 1) : d954 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1206 (pattern : Twelve) (guard : d1847 pattern = 1) : d961 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d961, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d1847, d961, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d961, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1205 pattern childGuard
    simpa only [d1847, d961, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1207 (pattern : Twelve) (guard : d1847 pattern = 1) : d958 pattern ≤ (0 : Int) + d987 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d958, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1013 pattern childGuard
    simpa only [d1847, d958, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d958, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d1847, d958, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1208 (pattern : Twelve) (guard : d1847 pattern = 1) : d967 pattern ≤ (0 : Int) + d995 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d967, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1206 pattern childGuard
    simpa only [d967, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d967, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1207 pattern childGuard
    simpa only [d967, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1209 (pattern : Twelve) (guard : d1847 pattern = 1) : d958 pattern ≤ (0 : Int) + d988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d958, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1019 pattern childGuard
    simpa only [d1847, d958, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d958, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d1847, d958, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1210 (pattern : Twelve) (guard : d1847 pattern = 1) : d960 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d960, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1024 pattern childGuard
    simpa only [d1847, d960, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d960, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1199 pattern childGuard
    simpa only [d1847, d960, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1211 (pattern : Twelve) (guard : d1847 pattern = 1) : d968 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d968, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1209 pattern childGuard
    simpa only [d968, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d968, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1210 pattern childGuard
    simpa only [d968, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1212 (pattern : Twelve) (guard : d1847 pattern = 1) : d966 pattern ≤ (0 : Int) + d997 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d966, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1207 pattern childGuard
    simpa only [d966, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d966, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d966, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1213 (pattern : Twelve) (guard : d1847 pattern = 1) : d972 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d972, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1211 pattern childGuard
    simpa only [d972, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d972, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1212 pattern childGuard
    simpa only [d972, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1214 (pattern : Twelve) (guard : d1847 pattern = 1) : d974 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d974, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1208 pattern childGuard
    simpa only [d974, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d974, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1213 pattern childGuard
    simpa only [d974, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1215 (pattern : Twelve) (guard : d1847 pattern = 1) : d976 pattern ≤ (0 : Int) + d1007 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d976, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1204 pattern childGuard
    simpa only [d976, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d976, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1214 pattern childGuard
    simpa only [d976, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1216 (pattern : Twelve) (guard : d0 pattern = 1) : d951 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1217 (pattern : Twelve) (guard : d1847 pattern = 1) : d962 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d962, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d1847, d962, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d962, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1216 pattern childGuard
    simpa only [d1847, d962, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1218 (pattern : Twelve) (guard : d1847 pattern = 1) : d969 pattern ≤ (0 : Int) + d998 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d969, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1217 pattern childGuard
    simpa only [d969, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d969, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1194 pattern childGuard
    simpa only [d969, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1219 (pattern : Twelve) (guard : d1847 pattern = 1) : d958 pattern ≤ (0 : Int) + d990 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d958, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1035 pattern childGuard
    simpa only [d1847, d958, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d958, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1193 pattern childGuard
    simpa only [d1847, d958, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1220 (pattern : Twelve) (guard : d1847 pattern = 1) : d968 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d968, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d968, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d968, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1200 pattern childGuard
    simpa only [d968, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1221 (pattern : Twelve) (guard : d1847 pattern = 1) : d972 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d972, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1220 pattern childGuard
    simpa only [d972, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d972, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1202 pattern childGuard
    simpa only [d972, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1222 (pattern : Twelve) (guard : d1847 pattern = 1) : d975 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d975, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1218 pattern childGuard
    simpa only [d975, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d975, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1221 pattern childGuard
    simpa only [d975, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1223 (pattern : Twelve) (guard : d1847 pattern = 1) : d977 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d977, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1222 pattern childGuard
    simpa only [d977, d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d977, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1214 pattern childGuard
    simpa only [d977, d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1224 (pattern : Twelve) (guard : d1847 pattern = 1) : d978 pattern ≤ (0 : Int) + d1009 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d978, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1215 pattern childGuard
    simpa only [d978, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d978, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1223 pattern childGuard
    simpa only [d978, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1225 (pattern : Twelve) (guard : d1847 pattern = 1) : d979 pattern ≤ (0 : Int) + d1010 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d979, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1224 pattern childGuard
    simpa only [d979, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d979, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1223 pattern childGuard
    simpa only [d979, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1226 (pattern : Twelve) (guard : d0 pattern = 1) : d1386 pattern ≤ (0 : Int) + d1355 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1227 (pattern : Twelve) (guard : d1847 pattern = 1) : d1393 pattern ≤ (0 : Int) + d1412 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1393, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1045 pattern childGuard
    simpa only [d1847, d1393, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1393, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1226 pattern childGuard
    simpa only [d1847, d1393, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1228 (pattern : Twelve) (guard : d0 pattern = 1) : d1388 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1229 (pattern : Twelve) (guard : d1847 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1413 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1394, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1052 pattern childGuard
    simpa only [d1847, d1394, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1394, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1228 pattern childGuard
    simpa only [d1847, d1394, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1230 (pattern : Twelve) (guard : d1847 pattern = 1) : d1398 pattern ≤ (0 : Int) + d1417 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1398, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1227 pattern childGuard
    simpa only [d1398, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1398, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1229 pattern childGuard
    simpa only [d1398, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1231 (pattern : Twelve) (guard : d0 pattern = 1) : d1386 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1232 (pattern : Twelve) (guard : d1847 pattern = 1) : d1395 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1395, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1057 pattern childGuard
    simpa only [d1847, d1395, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1395, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1231 pattern childGuard
    simpa only [d1847, d1395, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1233 (pattern : Twelve) (guard : d1847 pattern = 1) : d1399 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1399, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1232 pattern childGuard
    simpa only [d1399, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1399, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1229 pattern childGuard
    simpa only [d1399, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1234 (pattern : Twelve) (guard : d1847 pattern = 1) : d1403 pattern ≤ (0 : Int) + d1421 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1403, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1230 pattern childGuard
    simpa only [d1403, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1403, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1233 pattern childGuard
    simpa only [d1403, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1235 (pattern : Twelve) (guard : d1847 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1394, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1063 pattern childGuard
    simpa only [d1847, d1394, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1394, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1228 pattern childGuard
    simpa only [d1847, d1394, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1236 (pattern : Twelve) (guard : d0 pattern = 1) : d1391 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1237 (pattern : Twelve) (guard : d1847 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1396, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1070 pattern childGuard
    simpa only [d1847, d1396, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1396, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1236 pattern childGuard
    simpa only [d1847, d1396, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1238 (pattern : Twelve) (guard : d1847 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1400, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1235 pattern childGuard
    simpa only [d1400, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1400, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1237 pattern childGuard
    simpa only [d1400, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1239 (pattern : Twelve) (guard : d1847 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1420 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1401, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1229 pattern childGuard
    simpa only [d1401, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1401, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d1401, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1240 (pattern : Twelve) (guard : d1847 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1404, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1238 pattern childGuard
    simpa only [d1404, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1404, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1239 pattern childGuard
    simpa only [d1404, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1241 (pattern : Twelve) (guard : d1847 pattern = 1) : d1405 pattern ≤ (0 : Int) + d1423 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1405, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1234 pattern childGuard
    simpa only [d1405, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1405, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1240 pattern childGuard
    simpa only [d1405, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1242 (pattern : Twelve) (guard : d0 pattern = 1) : d1392 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1243 (pattern : Twelve) (guard : d1847 pattern = 1) : d1397 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1397, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1057 pattern childGuard
    simpa only [d1847, d1397, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1397, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1242 pattern childGuard
    simpa only [d1847, d1397, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1244 (pattern : Twelve) (guard : d1847 pattern = 1) : d1402 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1402, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1243 pattern childGuard
    simpa only [d1402, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1402, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1229 pattern childGuard
    simpa only [d1402, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1245 (pattern : Twelve) (guard : d1847 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1406, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1244 pattern childGuard
    simpa only [d1406, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1406, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1240 pattern childGuard
    simpa only [d1406, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1246 (pattern : Twelve) (guard : d1847 pattern = 1) : d1408 pattern ≤ (0 : Int) + d1425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1408, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1241 pattern childGuard
    simpa only [d1408, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1408, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1245 pattern childGuard
    simpa only [d1408, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1247 (pattern : Twelve) (guard : d1847 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1407, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1233 pattern childGuard
    simpa only [d1407, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1407, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1240 pattern childGuard
    simpa only [d1407, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1248 (pattern : Twelve) (guard : d1847 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1247 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1245 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1249 (pattern : Twelve) (guard : d1847 pattern = 1) : d1410 pattern ≤ (0 : Int) + d1426 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1410, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1246 pattern childGuard
    simpa only [d1410, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1410, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1248 pattern childGuard
    simpa only [d1410, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1250 (pattern : Twelve) (guard : d1847 pattern = 1) : d1411 pattern ≤ (0 : Int) + d1427 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1411, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1249 pattern childGuard
    simpa only [d1411, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1411, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1248 pattern childGuard
    simpa only [d1411, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1251 (pattern : Twelve) (guard : d0 pattern = 1) : d1694 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1252 (pattern : Twelve) (guard : d1847 pattern = 1) : d1697 pattern ≤ (0 : Int) + d1705 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1697, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1104 pattern childGuard
    simpa only [d1847, d1697, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1697, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1251 pattern childGuard
    simpa only [d1847, d1697, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1253 (pattern : Twelve) (guard : d1847 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1706 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1698, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1111 pattern childGuard
    simpa only [d1847, d1698, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1698, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1236 pattern childGuard
    simpa only [d1847, d1698, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1254 (pattern : Twelve) (guard : d1847 pattern = 1) : d1700 pattern ≤ (0 : Int) + d1709 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1700, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1252 pattern childGuard
    simpa only [d1700, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1700, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1253 pattern childGuard
    simpa only [d1700, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1255 (pattern : Twelve) (guard : d1847 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1707 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1698, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1116 pattern childGuard
    simpa only [d1847, d1698, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1698, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1236 pattern childGuard
    simpa only [d1847, d1698, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1256 (pattern : Twelve) (guard : d0 pattern = 1) : d1626 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1257 (pattern : Twelve) (guard : d1847 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1699, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1123 pattern childGuard
    simpa only [d1847, d1699, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1699, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1256 pattern childGuard
    simpa only [d1847, d1699, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1258 (pattern : Twelve) (guard : d1847 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1701, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1255 pattern childGuard
    simpa only [d1701, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1701, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1257 pattern childGuard
    simpa only [d1701, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1259 (pattern : Twelve) (guard : d1847 pattern = 1) : d1702 pattern ≤ (0 : Int) + d1711 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1702, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1253 pattern childGuard
    simpa only [d1702, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1702, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d1702, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
