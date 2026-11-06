/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons135
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c19040 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (12 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18816 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19039 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19041 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (12 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18827 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19042 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (12 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19040 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19041 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19043 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (12 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18972 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18837 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19044 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (12 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18822 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19043 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19045 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (12 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19035 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19044 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19046 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (12 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19037 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19047 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (12 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19045 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19046 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19048 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (12 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18980 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19047 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19049 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (12 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18827 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18898 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19050 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (12 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19049 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18829 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19051 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (12 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19050 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19052 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (12 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19048 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19051 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19053 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (12 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19042 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19052 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19054 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (12 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18873 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18821 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19055 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (12 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19054 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19043 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19056 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (12 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19037 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19055 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19057 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (12 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19045 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19056 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19058 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (12 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18856 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19057 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19059 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (12 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19049 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19060 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (12 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19058 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19059 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19061 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (12 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18893 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18846 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19062 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (12 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19044 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19061 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19063 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (12 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19055 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19064 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (12 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19062 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19063 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19065 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (12 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18997 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19064 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19066 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (12 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18898 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18847 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19067 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (12 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19066 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18899 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19068 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (12 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19067 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19069 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (12 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19065 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19068 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19070 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (12 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19060 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19069 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19071 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (12 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19052 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19072 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (12 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19070 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19071 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19073 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (12 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19053 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19072 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19074 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (12 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18827 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18855 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19075 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (12 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19074 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19076 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (12 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19040 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19075 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19077 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (12 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19049 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18915 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19078 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (12 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19077 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19079 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (12 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19048 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19078 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19080 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (12 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19076 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19079 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19081 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (12 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19049 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18895 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19082 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (12 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19081 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19083 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (12 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19058 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19082 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19084 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (12 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19066 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18941 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19085 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (12 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19084 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19086 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (12 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19065 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19085 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19087 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (12 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19083 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19086 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19088 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (12 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19079 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19089 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (12 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19087 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19088 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19090 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (12 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19080 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19089 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19091 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (12 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19073 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19090 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19092 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18963 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18965 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19093 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18964 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19092 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19094 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18966 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19095 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19093 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19094 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19096 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18964 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19097 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18967 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19096 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19098 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19092 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18839 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19099 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19092 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19100 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19098 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19099 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19101 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19097 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19100 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19102 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18998 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18968 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19103 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19102 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19104 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19101 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19103 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19105 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19095 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19104 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19106 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18967 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19098 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19107 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18998 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19108 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19106 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19107 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19109 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18839 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18851 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19110 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18839 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19111 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19109 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19110 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19112 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19102 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19111 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19113 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18999 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19114 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19112 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19113 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19115 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19108 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19114 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19116 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19104 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18828 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19117 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19115 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19116 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19118 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (12 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19105 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19117 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19119 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d0 pattern := by
  omega
theorem c19120 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d1 pattern := by
  change (0 : Int) ≤ (13 : Int) + 1
  decide
theorem c19121 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19119 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19120 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19122 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19119 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19121 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19123 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (13 : Int) + d1 pattern := by
  omega
theorem c19124 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (13 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19122 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19123 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19125 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (13 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19120 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19123 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19126 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (13 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19121 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19125 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19127 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (13 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19126 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19123 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19128 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (13 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19124 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19127 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19129 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (13 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19119 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19128 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19130 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d2 pattern := by
  change (0 : Int) ≤ (13 : Int) + 2
  decide
theorem c19131 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19119 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19130 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19132 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (13 : Int) + d3 pattern := by
  change (1 : Int) ≤ (13 : Int) + 3
  decide
theorem c19133 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (13 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19120 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19132 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19134 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (13 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19131 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19133 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19135 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (13 : Int) + d2 pattern := by
  change (1 : Int) ≤ (13 : Int) + 2
  decide
theorem c19136 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d4 pattern := by
  change (2 : Int) ≤ (13 : Int) + 4
  decide
theorem c19137 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (13 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19135 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19136 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19138 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d3 pattern := by
  change (2 : Int) ≤ (13 : Int) + 3
  decide
theorem c19139 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (13 : Int) + d5 pattern := by
  change (3 : Int) ≤ (13 : Int) + 5
  decide
theorem c19140 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (13 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19138 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19139 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19141 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (13 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19137 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19140 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19142 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (13 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19134 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19141 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19143 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (13 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19130 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19136 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19144 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (13 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19132 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19139 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19145 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (13 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19143 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19144 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19146 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (13 : Int) + d6 pattern := by
  omega
theorem c19147 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (13 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19145 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19146 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19148 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (13 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19142 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19147 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19149 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (13 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19122 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19148 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19150 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (13 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19129 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19149 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19151 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (13 : Int) + d30 pattern := by
  omega
theorem c19152 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (13 : Int) + d6 pattern := by
  change (3 : Int) ≤ (13 : Int) + 6
  decide
theorem c19153 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (13 : Int) + d6 pattern := by
  change (5 : Int) ≤ (13 : Int) + 6
  decide
theorem c19154 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19152 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19153 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19155 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (13 : Int) + d6 pattern := by
  change (4 : Int) ≤ (13 : Int) + 6
  decide
theorem c19156 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19155 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19146 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19157 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19154 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19156 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19158 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (13 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19119 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19157 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19159 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (13 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19151 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19158 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19160 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d2 pattern := by
  omega
theorem c19161 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19160 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19138 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19162 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19160 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19161 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19163 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (13 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19122 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19162 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19164 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19153 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19146 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19165 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19156 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19164 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19166 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (13 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19126 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19165 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19167 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (13 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19163 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19166 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19168 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (13 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19159 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19167 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19169 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (13 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19164 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19146 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19170 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (13 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19122 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19169 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19171 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (13 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19163 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19170 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19172 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19160 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19136 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19173 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (13 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19172 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19140 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19174 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (13 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19134 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19173 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19175 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (13 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19174 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19147 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19176 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (13 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19171 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19175 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19177 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (13 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19168 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19176 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19178 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (13 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19150 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19177 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19179 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (13 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19122 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19175 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
