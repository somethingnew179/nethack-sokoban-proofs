/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons071
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10080 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (8 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10078 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10079 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10081 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (8 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10013 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10080 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10082 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (8 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9914 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9863 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10083 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (8 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10082 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9915 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10084 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (8 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10083 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10085 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (8 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10081 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10084 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10086 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (8 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10076 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10085 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10087 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (8 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10068 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10088 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (8 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10086 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10087 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10089 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (8 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10069 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10088 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10090 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (8 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9843 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9871 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10091 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (8 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10090 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10092 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (8 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10056 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10091 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10093 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (8 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10065 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9931 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10094 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (8 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10093 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10095 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (8 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10064 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10094 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10096 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (8 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10092 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10095 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10097 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (8 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10065 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9911 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10098 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (8 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10097 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10099 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (8 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10074 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10098 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10100 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (8 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10082 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9957 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10101 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (8 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10100 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10102 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (8 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10081 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10101 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10103 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (8 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10099 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10102 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10104 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (8 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10095 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10105 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (8 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10103 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10104 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10106 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (8 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10096 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10105 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10107 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (8 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10089 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10106 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10108 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9979 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9981 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10109 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9980 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10108 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10110 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9982 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10111 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10109 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10110 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10112 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9980 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10113 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9983 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10112 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10114 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10108 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9855 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10115 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10108 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10116 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10114 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10115 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10117 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10113 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10116 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10118 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10014 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9984 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10119 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10118 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10120 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10117 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10119 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10121 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10111 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10120 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10122 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9983 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10114 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10123 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10014 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10124 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10122 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10123 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10125 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9855 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9867 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10126 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9855 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10127 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10125 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10126 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10128 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10118 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10127 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10129 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10015 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10130 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10128 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10129 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10131 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10124 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10130 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10132 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10120 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10133 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10131 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10132 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10134 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10121 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10133 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10135 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (2 : Int) + d116 pattern := by
  omega
theorem c10136 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (2 : Int) + d871 pattern := by
  omega
theorem c10137 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (2 : Int) + d1323 pattern := by
  omega
theorem c10138 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (2 : Int) + d1664 pattern := by
  omega
theorem c10139 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d0 pattern := by
  omega
theorem c10140 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d1 pattern := by
  change (0 : Int) ≤ (6 : Int) + 1
  decide
theorem c10141 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10139 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10140 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10142 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10139 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10141 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10143 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (6 : Int) + d1 pattern := by
  omega
theorem c10144 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (6 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10143 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10145 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (6 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10140 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10143 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10146 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (6 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10141 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10145 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10147 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (6 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10146 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10143 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10148 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (6 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10144 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10147 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10149 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (6 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10139 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10148 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10150 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d2 pattern := by
  change (0 : Int) ≤ (6 : Int) + 2
  decide
theorem c10151 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (6 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10139 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10150 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10152 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (6 : Int) + d3 pattern := by
  change (1 : Int) ≤ (6 : Int) + 3
  decide
theorem c10153 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (6 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10140 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10152 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10154 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (6 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10151 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10153 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10155 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (6 : Int) + d2 pattern := by
  change (1 : Int) ≤ (6 : Int) + 2
  decide
theorem c10156 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d4 pattern := by
  change (2 : Int) ≤ (6 : Int) + 4
  decide
theorem c10157 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (6 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10155 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10156 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10158 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d3 pattern := by
  change (2 : Int) ≤ (6 : Int) + 3
  decide
theorem c10159 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (6 : Int) + d5 pattern := by
  change (3 : Int) ≤ (6 : Int) + 5
  decide
theorem c10160 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (6 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10158 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10159 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10161 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (6 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10157 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10160 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10162 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (6 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10154 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10161 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10163 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (6 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10150 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10156 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10164 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (6 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10152 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10159 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10165 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (6 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10163 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10164 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10166 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (6 : Int) + d6 pattern := by
  omega
theorem c10167 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (6 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10165 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10168 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (6 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10162 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10167 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10169 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (6 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10168 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10170 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (6 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10149 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10169 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10171 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (6 : Int) + d30 pattern := by
  omega
theorem c10172 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (6 : Int) + d6 pattern := by
  change (3 : Int) ≤ (6 : Int) + 6
  decide
theorem c10173 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (6 : Int) + d6 pattern := by
  change (5 : Int) ≤ (6 : Int) + 6
  decide
theorem c10174 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10172 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10173 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10175 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (6 : Int) + d6 pattern := by
  change (4 : Int) ≤ (6 : Int) + 6
  decide
theorem c10176 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10175 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10177 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10174 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10176 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10178 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (6 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10139 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10177 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10179 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (6 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10171 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10178 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10180 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d2 pattern := by
  omega
theorem c10181 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10180 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10158 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10182 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10180 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10181 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10183 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (6 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10182 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10184 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10173 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10185 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10176 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10184 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10186 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (6 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10146 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10185 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10187 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (6 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10186 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10188 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (6 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10179 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10187 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10189 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (6 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10184 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10190 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (6 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10189 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10191 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (6 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10190 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10192 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (6 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10180 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10156 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10193 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (6 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10192 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10160 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10194 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (6 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10154 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10193 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10195 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (6 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10194 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10167 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10196 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (6 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10191 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10195 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10197 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (6 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10188 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10196 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10198 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (6 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10170 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10197 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10199 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (6 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10195 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10200 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (6 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10149 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10199 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10201 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (6 : Int) + d56 pattern := by
  omega
theorem c10202 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (6 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10146 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10203 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (6 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10202 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10204 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (6 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10201 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10203 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10205 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (6 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10142 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10166 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10206 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (6 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10205 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10207 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (6 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10206 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10195 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10208 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (6 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10204 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10207 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10209 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (6 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10200 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10208 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10210 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (6 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10198 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10209 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10211 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (6 : Int) + d3 pattern := by
  omega
theorem c10212 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (6 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10146 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10211 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10213 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (6 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10212 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10214 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (6 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10171 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10213 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10215 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (6 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10183 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10195 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10216 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (6 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10214 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10215 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10217 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (6 : Int) + d59 pattern := by
  omega
theorem c10218 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (6 : Int) + d4 pattern := by
  omega
theorem c10219 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (6 : Int) + d5 pattern := by
  change (4 : Int) ≤ (6 : Int) + 5
  decide
end NetHack.Sokoban21.Diagram
